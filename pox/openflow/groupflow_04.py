#!/usr/bin/python
# -*- coding: utf-8 -*-

#  Copyright 2014 Alexander Craig
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.

"""
A POX module implementation of multicast routing, supported by management of group state using the IGMP manager module.

Implementation adapted from NOX-Classic CastFlow implementation provided by caioviel. Multicast routing records are stored for each 
combination of multicast group and source address. For each of these records the GroupFlow module will calculate a shortest path tree 
using Dijkstra's algorithm from the multicast source to all routers in the network (where each edge is weighted according to the number 
of hops from the multicast source). Branches of this tree which correspond to active multicast receivers are installed into the network
through OpenFlow, and the spanning tree is only recalculated when the network topology changes. This should enable rapid changes of 
multicast group, as there is no need to completely recalculate the multicast tree when new receivers join a group.

The following command line arguments are supported:

* tree_encoding_mode: Determines what encoding method is used to convert multicast trees to Openflow rules. Supported options:
  'standard': Trees are encoded using standard techniques (i.e. one group and source specific entry is installed at every node participating
  in a multicast distribution tree.
  'bloom_filter': Bloom filter based encoding is used. A single flow is configured on all nodes in the network, which matches against a reserved VLAN ID
  (hardcoded), and applies a bloom filter forwarding action. Addition flow entries are only required for ingress/egress nodes for each group and source pair.
* link_weight_type: Determines the method by which link weights are scaled with link utilization. Supported options are 'linear'
  (link weight scales as a linear function of utilization) or 'exponential' (link weight grows exponentially with increasing utilization).
  Default: linear
* static_link_weight: Determines the static weight which is applied to all links regardless of utilization.
  Default: 1
* util_link_weight: Determines the scaling factor by which utilization based link weight will be multiplied. Higher values cause the current
  traffic state to be more heavily weighted in routing (relative to the network topology). Note that setting this to 0 with either link
  weight type will produce shortest cost trees in terms of number of hops only.
  Default: 10
* flow_replacement_mode: Determines the manner in which replacement of existing flows is triggered. Supported options:
  'none': Existing flows are never replaced.
  'periodic': Existing flows are periodically replaced.
  'cong_threshold': In this mode, flow replacement is triggered by the FlowTracker module reporting congestion on a link traversed by the flow.
  Upon receiving a LinkUtilizationEvent, the GroupFlow module will attempt to replace the largest flows traversing the link until the link is
  brought back under its congestion threshold.
  Default: 'none'
* flow_replacement_interval: Determines the flow replacement interval in a mode specific fashion (always specified in seconds): 
  'none': Has no effect
  'periodic': Sets the periodic interval at which flows are replaced.
  'cong_threshold': Sets the minimum interval that must elapse after flow placement, before the flow can be replaced.
  Default: 10

Depends on openflow.igmp_manager, misc.groupflow_event_tracer (optional)

Created on July 16, 2013

Author: Alexander Craig - alexcraig1@gmail.com
"""

from collections import defaultdict
from sets import Set
from heapq import heappop, heappush
import math
import mpmath
import time
from bitarray import bitarray
from random import randint
import numpy as np

# POX dependencies
from pox.openflow.discovery_04 import Discovery
from pox.core import core
from pox.lib.revent import *
from pox.misc.groupflow_event_tracer_04 import *
from pox.openflow.flow_tracker_04 import *
from pox.lib.util import dpid_to_str
import pox.lib.packet as pkt
from pox.lib.packet.igmp import *   # Required for various IGMP variable constants
from pox.lib.packet.ethernet import *
import pox.openflow.libopenflow_04 as of
from pox.lib.addresses import IPAddr, EthAddr
from pox.lib.recoco import Timer
from pox.lib.bloomflow_shim import bloom_filter, encode_elias_gamma, decode_elias_gamma, bitarray_to_str
from pox.openflow.igmp_manager_04 import MulticastTopoEvent
import sys
import itertools
import csv

log = core.getLogger()

# Constants used to determine which link weighting scheme is used
LINK_WEIGHT_LINEAR = 1
LINK_WEIGHT_EXPONENTIAL = 2

STATIC_LINK_WEIGHT = 1    # Scaling factor for link weight which is statically assigned (implements shortest hop routing if no dynamic link weight is set)
UTILIZATION_LINK_WEIGHT = 10   # Scaling factor for link weight which is determined by current link utilization

# Constants used to determine which tree encoding scheme is used
TREE_ENCODING_STANDARD = 0
TREE_ENCODING_BLOOM_FILTER = 1

# Constants used to determine which method of filter length iteration is used
FILTER_LEN_ITER_MINIMUM_LENGTH = 0
FILTER_LEN_ITER_EXPECTED_ALTERNATING = 1
FILTER_LEN_ITER_EXPECTED_LOW_FIRST = 2
FILTER_LEN_ITER_EXPECTED_HIGH_FIRST = 3

FILTER_LEN_ITER_DEFAULT = FILTER_LEN_ITER_EXPECTED_HIGH_FIRST

# Constant which determines the maximum filter length to be considered in any individual bloom filter stage
MIN_FILTER_LEN_BITS = 1
MAX_FILTER_LEN_BITS = 200

# Constant which determines the VLAN ID reserved for bloom filter matching
BLOOMFLOW_RESERVED_VLAN_ID = 2042
BLOOMFLOW_RESERVED_VLAN_ETHERTYPE = 0x8100

# Default flow replacement interval
FLOW_REPLACEMENT_INTERVAL_SECONDS = 10

# Constants to determine flow replacement mode
NO_FLOW_REPLACEMENT = 0
PERIODIC_FLOW_REPLACEMENT = 1
CONG_THRESHOLD_FLOW_REPLACEMENT = 2

# Constants used for expected filter length import from CSV
EXP_FILTER_LEN_CSV_FILE = "exp_filter_len.csv"
EXP_FILTER_LEN_CSV_MAX_LINKS = 300

# Determines the prefix used for rewritten destination IPs
# when using multi-trees with standard flow installation
MTREE_DST_IP_PREFIX = "123.231."

# Developer constants
# The below constants enable/configure experimental features which have not yet been integrated into the module API
ENABLE_OUT_OF_ORDER_PACKET_DELIVERY = False
FIXED_BLOOM_IDS = True
RANDOM_NUM_IDS_PER_ROUTER = False
FIXED_BIDS_PER_ROUTER = 20
RANDOM_BIDS_PER_ROUTER_MIN = 30
RANDOM_BIDS_PER_ROUTER_MAX = 60 

# Utility Functions
def expi_inverse(x, tolerance = 0.0000001):
    # Calculates the exponential inverse function
    # See http://math.stackexchange.com/questions/853178/numerical-inverse-of-logarithmic-integral/853192#853192
    u = [];
    u.append(0.5);
    inverse_in_tolerance = False
    cur_u_index = 0
    
    while not inverse_in_tolerance:
        cur_u_index = cur_u_index + 1
        zn = u[cur_u_index - 1]
        delta_n = float(mpmath.li(zn)) - x
        u.append(zn - (delta_n * np.log(zn) * ((1 + (delta_n / (2*zn)))**(-1))))
        
        if abs(u[cur_u_index] - u[cur_u_index - 1]) < tolerance:
            inverse_in_tolerance = True
        
        if cur_u_index > 10:
            break

    return np.log(u[cur_u_index])
    
def expected_filter_len_calc(alpha, beta, expi_inverse_tolerance = 0.0000001):
    # Calculates the expected false-positive-free bloom filter length, given
    # the number of set elements to include (alpha) and the number of set
    # elements to exclude (beta)
    if alpha == 0 or beta == 0:
        exp_fpf_len = 1
    else:
        t = expi_inverse(-(np.log(2)**3) / alpha, 0.0000001)
        exp_fpf_len = int((alpha * np.log( (-beta) / t)) / (np.log(2)**2))
        if exp_fpf_len < 1:
            exp_fpf_len = 1
    # log.info('exp_fpf_len, alpha = ' + str(alpha) + ', beta = ' + str(beta) + ', len = ' + str(exp_fpf_len))
    return exp_fpf_len
    
def compare_edges(edge1, edge2):
    if edge1[0] < edge2[0]:
        return -1
    elif edge1[0] > edge1[0]:
        return 1
    else:
        if edge1[1] < edge2[1]:
            return -1
        elif edge1[1] > edge1[1]:
            return 1
    return 0

class MulticastPath(object):
    """Manages multicast route calculation and installation for a single pair of multicast group and multicast sender."""

    def __init__(self, src_ip, src_router_dpid, ingress_port, dst_mcast_address, groupflow_manager, groupflow_trace_event = None):
        self.src_ip = src_ip
        self.ingress_port = ingress_port
        self.src_router_dpid = src_router_dpid
        self.dst_mcast_address = dst_mcast_address
        self.num_multi_trees = groupflow_manager.num_multi_trees
        # self.path_tree_map[mtree_index][router_dpid] = Complete path from receiver router_dpid to src for multi_tree mtree_index
        self.path_tree_map = [] # defaultdict(lambda : None)     # self.path_tree_map[mtree_index][router_dpid] = Complete path from receiver router_dpid to src for multi_tree mtree_index
        for i in range(0, self.num_multi_trees):
            self.path_tree_map.append(defaultdict(lambda : None))
        self.weighted_topo_graph = []
        self.node_list = []                 # List of all managed router dpids
        self.installed_node_list = []       # List of all router dpids with rules currently installed
        self.receivers = []                 # Tuples of (router_dpid, port)
        self.groupflow_manager = groupflow_manager
        self.flow_cookie = self.groupflow_manager.get_new_mcast_group_cookie()
        self.calc_path_tree_dijkstras(groupflow_trace_event)
        self._last_flow_replacement_time = None
        self._flow_replacement_timer = None

    def calc_path_tree_dijkstras(self, groupflow_trace_event = None):
        """Calculates a shortest path tree from the group sender to all network switches, and caches the resulting tree.

        Note that this function does not install any flow modifications."""
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_tree_calc_start_time(self.dst_mcast_address, self.src_ip)
        self._last_flow_replacement_time = time.time()
    
        self._calc_link_weights()
        
        for mtree_index in range(0, self.num_multi_trees):
            if mtree_index == 0:
                edges = self.weighted_topo_graph
                edges = sorted(edges, cmp = compare_edges)
            else:
                edges = self.multi_tree_increment_topo_graph(edges, self.path_tree_map[mtree_index - 1])
                
            nodes = set(self.node_list)
            graph = defaultdict(list)
            #log.debug('====\nDjikstra algo using weighted edge graph:')
            for src,dst,cost in edges:
                #log.debug(dpid_to_str(src) + ' -> ' + dpid_to_str(dst) + ' W: ' + str(cost))
                graph[src].append((cost, dst))
            #log.debug('====')
         
            path_tree_map = defaultdict(lambda : None)
            queue, seen = [(0,self.src_router_dpid,())], set()
            while queue:
                (cost,node1,path) = heappop(queue)
                if node1 not in seen:
                    seen.add(node1)
                    path = (node1, path)
                    path_tree_map[node1] = path
         
                    for next_cost, node2 in graph.get(node1, ()):
                        if node2 not in seen:
                            new_path_cost = cost + next_cost
                            heappush(queue, (new_path_cost, node2, path))
            
            self.path_tree_map[mtree_index] = path_tree_map
            
            log.debug('Calculated shortest path tree ' + str(mtree_index) + ' for source at router_dpid: ' + dpid_to_str(self.src_router_dpid))
            for node in self.path_tree_map[mtree_index]:
                log.debug('Path to Node ' + dpid_to_str(node) + ': ' + str(self.path_tree_map[mtree_index][node]))
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_tree_calc_end_time()
    
    def _calc_link_weights(self):
        """Calculates link weights for all links in the network to be used by calc_path_tree_dijkstras().

        The cost assigned to each link is based on the link's current utilization (as determined by the FlowTracker
        module), and the exact manner in which utilization is converted to a link wieght is determined by
        groupflow_manager.link_weight_type. Valid options are LINK_WEIGHT_LINEAR and LINK_WEIGHT_EXPONENTIAL. Both options
        include a static weight which is always assigned to all links (determined by groupflow_manager.static_link_weight),
        and a dynamic weight which is based on the current utilization (determined by
        groupflow_manager.utilization_link_weight). Setting groupflow_manager.utilization_link_weight to 0 will always
        results in shortest hop routing.
        """
        curr_topo_graph = self.groupflow_manager.topology_graph
        self.node_list = list(self.groupflow_manager.node_set)
        
        weighted_topo_graph = []
        current_util = core.openflow_flow_tracker.get_max_flow_utilization(self.flow_cookie) / core.openflow_flow_tracker.link_max_bw
        log.info('Current utilization of flow ' + str(self.flow_cookie) + ': ' + str(current_util * core.openflow_flow_tracker.link_max_bw) + ' Mbps')
        
        for edge in curr_topo_graph:
            output_port = self.groupflow_manager.adjacency[edge[0]][edge[1]]
            raw_link_util = core.openflow_flow_tracker.get_link_utilization_normalized(edge[0], output_port);
            link_util_mcast_flow = core.openflow_flow_tracker.get_flow_utilization_normalized(edge[0], output_port, self.flow_cookie)
            
            link_util = max(0, (raw_link_util * (1 - link_util_mcast_flow)))
            
            # link_util = raw_link_util # Uncommenting this line will cause flows to reroute around their own traffic, good for testing
            
            # Current utilization here is doubled as a simple attempt to handle variability in flow rates
            if link_util + (current_util * 2) > 1:
                link_util = 1
            
            link_weight = 1
            
            if self.groupflow_manager.util_link_weight == 0:
                link_weight = self.groupflow_manager.static_link_weight
            else:
                if self.groupflow_manager.link_weight_type == LINK_WEIGHT_LINEAR:
                    if link_util >= 1:
                        link_weight = sys.float_info.max / core.openflow_flow_tracker.get_num_tracked_links()
                    else:
                        link_weight = min(self.groupflow_manager.static_link_weight + (self.groupflow_manager.util_link_weight * link_util),
                                sys.float_info.max / core.openflow_flow_tracker.get_num_tracked_links())
                elif self.groupflow_manager.link_weight_type == LINK_WEIGHT_EXPONENTIAL:
                    if link_util >= 1:
                        link_weight = sys.float_info.max / core.openflow_flow_tracker.get_num_tracked_links()
                    else:
                        link_weight = min(self.groupflow_manager.static_link_weight + (self.groupflow_manager.util_link_weight * ((1 / (1 - link_util)) - 1)),
                                sys.float_info.max / core.openflow_flow_tracker.get_num_tracked_links())
                
                log.debug('Router DPID: ' + dpid_to_str(edge[0]) + ' Port: ' + str(output_port) + 
                        ' TotalUtil: ' + str(raw_link_util) + ' FlowUtil: ' + str(link_util_mcast_flow) + ' OtherFlowUtil: ' + str(link_util) 
                        + ' Weight: ' + str(link_weight))

            weighted_topo_graph.append([edge[0], edge[1], link_weight])
        self.weighted_topo_graph = weighted_topo_graph
        
        #log.debug('Calculated link weights for source at router_dpid: ' + dpid_to_str(self.src_router_dpid))
        #for edge in self.weighted_topo_graph:
        #    log.debug(dpid_to_str(edge[0]) + ' -> ' + dpid_to_str(edge[1]) + ' W: ' + str(edge[2]))
    
    
    def multi_tree_increment_topo_graph(self, weighted_topo_graph, previous_tree_path_map):
        # First, determine the set of edges which were used in the previous tree
        calculated_path_router_dpids = []
        prev_tree_edge_set = Set()
        reception_state = self.groupflow_manager.get_reception_state(self.dst_mcast_address, self.src_ip)
        for receiver in reception_state:
            if receiver[0] == self.src_router_dpid:
                continue
            if receiver[0] in calculated_path_router_dpids:
                continue
            receiver_path = previous_tree_path_map[receiver[0]]
            while receiver_path[1]:
                prev_tree_edge_set.add((receiver_path[1][0], receiver_path[0]))
                receiver_path = receiver_path[1]
                
        # Next, iterate through all edges in the provided weighted_topo_graph, and increase their weight by 
        # self.groupflow_manager.static_link_weight if they were used in the previous tree
        log.debug('Increasing weights of previously used edges:')
        for edge in weighted_topo_graph:
            edge_tuple = (edge[0], edge[1])
            if edge_tuple in prev_tree_edge_set:
                edge[2] = edge[2] + self.groupflow_manager.static_link_weight
                log.debug(dpid_to_str(edge[0]) + ' -> ' + dpid_to_str(edge[1]) + ' W: ' + str(edge[2]))
        
        return weighted_topo_graph
        
    
    def install_openflow_rules(self, groupflow_trace_event = None):
        """Selects routes for active receivers from the cached shortest path tree, and installs/removes OpenFlow rules accordingly.
        
        The method of tree encoding used is determined by the tree_encoding_mode attribute of the GroupFlowManager.
        """
        if self.groupflow_manager.tree_encoding_mode == TREE_ENCODING_STANDARD:
            self.install_openflow_rules_standard(groupflow_trace_event)
        elif self.groupflow_manager.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            self.install_openflow_rules_bloom_filter(groupflow_trace_event)

    def install_openflow_rules_bloom_filter(self, groupflow_trace_event = None):
        """Selects routes for active receivers from the cached shortest path tree, and installs/removes OpenFlow rules using bloom filter tree encoding."""        
        reception_state = self.groupflow_manager.get_reception_state(self.dst_mcast_address, self.src_ip)
        num_receivers = 0
        for receiver in reception_state:
            num_receivers += 1
        log.info('Number of Receivers: ' + str(num_receivers))
        log.debug('Reception state for ' + str(self.dst_mcast_address) + ': ' + str(reception_state))
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_route_processing_start_time(self.dst_mcast_address, self.src_ip)
        
        # Edges to install is a dictionary in this case, keyed by the hop distance from the root node of the tree
        # Multi-tree extensions - all three of these data structures now use the multi-tree index as their first key
        edges_to_install = []
        node_hop_distance = []
        calculated_path_router_dpids = []
        complete_shim_header = []
        for mtree_index in range(0, self.num_multi_trees):
            edges_to_install.append(defaultdict(lambda : None))
            node_hop_distance.append(defaultdict(lambda : None))
            node_hop_distance[mtree_index][self.src_router_dpid] = 0
            calculated_path_router_dpids.append([])
            complete_shim_header.append(None)
        
        # First, parse the path tree maps generated by the Djikstra algorithm to determine which edges should be
        # added for each tree
        for mtree_index in range(0, self.num_multi_trees):
            # log.info('Multi-tree #' + str(mtree_index) + ':')
            for receiver in reception_state:
                if receiver[0] == self.src_router_dpid:
                    continue
                if receiver[0] in calculated_path_router_dpids:
                    continue
                
                receiver_path = self.path_tree_map[mtree_index][receiver[0]]
                # log.info('Receiver path for receiver ' + str(receiver[0]) + ': ' + str(receiver_path))
                if receiver_path is None:
                    log.warn('Path could not be determined for receiver ' + dpid_to_str(receiver[0]) + ' (network is not fully connected)')
                    continue
                
                receiver_edge_list = []
                # Build the path for this particular receiver
                while receiver_path[1]:
                    receiver_edge_list.append((receiver_path[1][0], receiver_path[0]))
                    receiver_path = receiver_path[1]
                # Now that the length of the receiver path is known, install it into the dictionary of edges
                # keyed by distance from the root node
                hop_distance = 0
                receiver_edge_list.reverse()
                for edge in receiver_edge_list:
                    if edges_to_install[mtree_index][hop_distance] is None:
                        edges_to_install[mtree_index][hop_distance] = Set()
                    edges_to_install[mtree_index][hop_distance].add(edge)
                    node_hop_distance[mtree_index][edge[0]] = hop_distance
                    node_hop_distance[mtree_index][edge[1]] = hop_distance + 1
                    hop_distance += 1
                
                calculated_path_router_dpids[mtree_index].append(receiver[0])
            
            #log.debug('Calculated tree ' + str(mtree_index) + ' for ' + str(self.dst_mcast_address) + ':')
            #log.debug('Participating nodes by hop distance:')
            #for node in node_hop_distance[mtree_index]:
            #    log.info(dpid_to_str(node) + ' - Hop distance: ' + str(node_hop_distance[mtree_index][node]))
        
        # DEBUG
        #for mtree_index in range(0, self.num_multi_trees):
        #    num_interswitch_links = 0
        #    for hop_distance in edges_to_install[mtree_index]:
        #        num_interswitch_links += len(edges_to_install[mtree_index][hop_distance])
        #    log.info('Total # of Inter-Switch Links MTree #' + str(mtree_index) + ': ' + str(num_interswitch_links))
        
        
        num_hash_and_check_ops = 0
        num_hash_and_set_ops = 0
        
        num_tested_lens_aggregated = []
        for mtree_index in range(0, self.num_multi_trees):
            for hop_distance in edges_to_install[mtree_index]:
                #if hop_distance == 0:
                    # First hop is always implemented with explicit output actions, does not require bloom filter calculation
                #    continue
                #log.info('Filter stage: ' + str(hop_distance))
                if not groupflow_trace_event is None:
                    num_hash_and_check_ops = 0
                    num_hash_and_set_ops = 0
                    groupflow_trace_event.set_bloom_filter_calc_start_time()
                
                # Calculate the set of bloom identifiers which must be included and excluded for this filter stage
                include_bloom_ids = []
                for edge in edges_to_install[mtree_index][hop_distance]:
                    #log.info('Include edge: ' + dpid_to_str(edge[0]) + ' -> ' + dpid_to_str(edge[1]) + ' (BID: ' + str(self.groupflow_manager.bloom_id_adjacency[edge[0]][edge[1]]) + ')')
                    include_bloom_ids.append(self.groupflow_manager.bloom_id_adjacency[edge[0]][edge[1]])
                
                
                exclude_bloom_ids = []
                if hop_distance > 0:
                    for edge in edges_to_install[mtree_index][hop_distance - 1]:
                        for dpid in self.groupflow_manager.bloom_id_adjacency[edge[1]]:
                            if dpid == edge[0]:
                                # Reverse edges of the tree do not need to be considered for exclusion
                                continue
                            if self.groupflow_manager.bloom_id_adjacency[edge[1]][dpid] is not None:
                                if self.groupflow_manager.bloom_id_adjacency[edge[1]][dpid] not in include_bloom_ids:
                                    #log.warn('Exclude edge: ' + dpid_to_str(edge[1]) + ' -> ' + dpid_to_str(dpid))
                                    exclude_bloom_ids.append(self.groupflow_manager.bloom_id_adjacency[edge[1]][dpid])
                else:
                    # Special case for root node, can't check outgoing edges of previous tree depth, as this
                    # is the root of the tree
                    for dpid in self.groupflow_manager.bloom_id_adjacency[self.src_router_dpid]:
                            if self.groupflow_manager.bloom_id_adjacency[self.src_router_dpid][dpid] is not None:
                                if self.groupflow_manager.bloom_id_adjacency[self.src_router_dpid][dpid] not in include_bloom_ids:
                                    #log.warn('Exclude edge: ' + dpid_to_str(edge[1]) + ' -> ' + dpid_to_str(dpid))
                                    exclude_bloom_ids.append(self.groupflow_manager.bloom_id_adjacency[self.src_router_dpid][dpid])
                
                exclude_bloom_ids.sort()
                
                # Build the range of values which will be tested for filter membership
                expected_fpf_len = self.groupflow_manager.expected_filter_len(len(include_bloom_ids), len(exclude_bloom_ids))
                filter_len_test_range = self.groupflow_manager.get_filter_len_interval(expected_fpf_len)
                
                # log.info('filter_len_test_range = ' + str(filter_len_test_range))
                #if not groupflow_trace_event is None:
                #    groupflow_trace_event.set_bloom_filter_calc_start_time()
                
                num_tested_lens = 0
                stage_filter = bloom_filter(1, 1)
                false_positive_free = False
                for filter_len in filter_len_test_range:
                    num_tested_lens += 1
                    num_hash_functions = math.ceil(math.log(2.0) * (float(filter_len) / float(len(include_bloom_ids))))
                    stage_filter.clear_and_resize(filter_len, num_hash_functions)
                    
                    # Construct the bloom filter
                    for bloom_id in include_bloom_ids:
                        stage_filter.add_member(bloom_id)
                        num_hash_and_set_ops += num_hash_functions
                        
                    # Test the filter for false positives
                    false_positive_free = True
                    for bloom_id in exclude_bloom_ids:
                        if stage_filter.check_member(bloom_id):
                            num_hash_and_check_ops += stage_filter.num_hashes_last_op
                            false_positive_free = False
                            break
                        else:
                            num_hash_and_check_ops += stage_filter.num_hashes_last_op
                    
                    if false_positive_free:
                        break
                        
                if not groupflow_trace_event is None:
                    groupflow_trace_event.set_bloom_filter_calc_end_time()
                    groupflow_trace_event.add_hash_and_set_ops(num_hash_and_set_ops)
                    groupflow_trace_event.add_hash_and_check_ops(num_hash_and_check_ops)
                    groupflow_trace_event.add_tested_lens(num_tested_lens)
                    
                
                # num_tested_lens_aggregated.append(num_tested_lens)
                # log.info('num_tested_lens = ' + str(num_tested_lens))
                if false_positive_free:
                    #log.debug('Found false positive free bloom filter:')
                    #log.debug(stage_filter.debug_str())
                    if complete_shim_header[mtree_index] is None:
                        complete_shim_header[mtree_index] = stage_filter.pack_shim_header()
                    else:
                        complete_shim_header[mtree_index] = complete_shim_header[mtree_index] + stage_filter.pack_shim_header()
                    #log.info('Calculated stage shim header: ' + bitarray_to_str(stage_filter.pack_shim_header()))
                else:
                    # TODO: HANDLE THIS ERROR CONDITION MORE GRACEFULLY
                    if not groupflow_trace_event is None:
                        groupflow_trace_event.set_route_processing_end_time()
                        core.groupflow_event_tracer.archive_trace_event(groupflow_trace_event)
                    log.warn('BLOOM FILTER ERROR: Failed to find false positive free bloom filter with length under ' + str(MAX_FILTER_LEN_BITS) + ' bits.')
                    return
                    
                # log.debug('=====')
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_route_processing_end_time()
        
        # log.info('num_tested_lens = ' + str(num_tested_lens_aggregated))
        # log.info('sum_num_tested_lens = ' + str(sum(num_tested_lens_aggregated)))
        
        for mtree_index in range(0, self.num_multi_trees):
            if complete_shim_header[mtree_index] is not None:
                log.info('Calculated complete shim header - Group: ' + str(self.dst_mcast_address) + ' MultiTree: ' + str(mtree_index) + ' Filter_Len: ' + str(len(complete_shim_header[mtree_index])))
                log.info(bitarray_to_str(complete_shim_header[mtree_index]))
                if len(complete_shim_header[mtree_index]) > 320:
                    log.warn('BLOOM FILTER ERROR: Calculated shim header is greater than 320 bits.')
                    # TODO: HANDLE THIS ERROR CONDITION MORE GRACEFULLY
                    if not groupflow_trace_event is None:
                        core.groupflow_event_tracer.archive_trace_event(groupflow_trace_event)
                    return
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_flow_installation_start_time()        
        
        # Now that the shim header has been calculated, install the required OpenFlow rules
        # Dictionary is keyed by the dpid on which the rule will be installed
        flow_mods = defaultdict(lambda : None)
        
        # A group of type SELECT must be created, with a bucket of actions for each multi-tree
        # This group is given an id equal to the flow cookie of this group
        group_select_msg = of.ofp_group_mod()
        group_select_msg.command = 0   # OFPGC_ADD
        group_select_msg.type = 1      # OFPGT_SELECT
        group_select_msg.group_id = self.flow_cookie
        
        for mtree_index in range(0, self.num_multi_trees):           
            log.info('Generating bucket for mtree ' + str(mtree_index))
            
            mtree_bucket = of.ofp_bucket()
            mtree_bucket.watch_port = 0xffffffff # OFPP_ANY
            mtree_bucket.watch_group = 0xffffffff # OFPG_ANY
            mtree_bucket.weight = 10
            
            bucket_actions = []
            
            '''
            vlan_push_action = of.ofp_action_push_vlan()
            vlan_push_action.ethertype = BLOOMFLOW_RESERVED_VLAN_ETHERTYPE
            bucket_actions.append(vlan_push_action)
            vlan_set_action = of.ofp_action_set_field()
            vlan_set_action.oxm_field = of.oxm_match_field(oxm_field = of.oxm_ofb_match_fields_rev_map['OFPXMT_OFB_VLAN_VID'],
                    oxm_length = 2, data = struct.pack('!H', BLOOMFLOW_RESERVED_VLAN_ID | 0x1000), value = str(BLOOMFLOW_RESERVED_VLAN_ID | 0x1000),)
            vlan_set_action.pack()
            bucket_actions.append(vlan_set_action)
            '''
            
            if complete_shim_header[mtree_index] is not None:
                # A tree exists with more than 1 hop, apply the VLAN ID and shim header at the root node
                # log.debug('The generated tree contains more than 1 hop, applying shim header')
                shim_action = of.ofp_action_push_shim_header()
                shim_header_bytes = complete_shim_header[mtree_index].tobytes()
                for i in range(0, len(shim_header_bytes)):
                    shim_action.shim[i] = shim_header_bytes[i]
                shim_action.shim_len = len(shim_header_bytes)
                bucket_actions.append(shim_action)
                log.info('Added shim header and VLAN tag actions on ' + dpid_to_str(self.src_router_dpid))
            
            bucket_actions.append(of.ofp_action_output(port = of.OFPP_BLOOM_PORTS))
            #for edge in edges_to_install[mtree_index][0]:
            #    bucket_actions.append(of.ofp_action_output(port = self.groupflow_manager.adjacency[edge[0]][edge[1]]))
            #log.debug('Added output action on ' + dpid_to_str(self.src_router_dpid) + ' Port: ' + str(self.groupflow_manager.adjacency[edge[0]][edge[1]]))
            
            #log.info('Ingress Actions mtree ' + str(mtree_index) + ', output_port ' + str(self.groupflow_manager.adjacency[edge[0]][edge[1]]) + ': ' + str(bucket_actions))
            mtree_bucket.actions = bucket_actions
            group_select_msg.buckets.append(mtree_bucket)
        
        # Next, generate a flow mod for the ingress switch that directs packets to the previously generated group
        msg = of.ofp_flow_mod()
        msg.hard_timeout = 0
        msg.idle_timeout = 0
        msg.priority += 4
        if self.src_router_dpid in self.installed_node_list:
            msg.command = of.OFPFC_MODIFY
        else:
            msg.command = of.OFPFC_ADD
        match = of.ofp_match(dl_type = 0x800, nw_dst = self.dst_mcast_address, nw_src = self.src_ip)
        msg.match = match
        msg.cookie = self.flow_cookie
        flow_mods[self.src_router_dpid] = msg
        log.debug('Generated flow mod for root node ' + dpid_to_str(self.src_router_dpid))
        # Generate the group action
        group_action = of.ofp_action_group()
        group_action.group_id = self.flow_cookie
        msg.actions.append(group_action)
        msg.instructions = []
        msg.instructions.append(of.ofp_instruction_actions_apply(
                                actions = msg.actions, 
                                type = 4, # OFPIT_APPLY_ACTION
                                ))
        log.info("Ingress Flow Mod Instructions: " + str(msg.instructions))
        
        # Now, loop through all receivers, and generate group specific forwarding entries as necessary
        for receiver in reception_state:
            if receiver[0] not in flow_mods:
                # Generate a new flow mod
                msg = of.ofp_flow_mod()
                msg.hard_timeout = 0
                msg.idle_timeout = 0
                if receiver[0] in self.installed_node_list:
                    msg.command = of.OFPFC_MODIFY
                else:
                    msg.command = of.OFPFC_ADD
                msg.cookie = self.flow_cookie
                match = of.ofp_match(dl_type = 0x800, nw_dst = self.dst_mcast_address, nw_src = self.src_ip, dl_vlan = BLOOMFLOW_RESERVED_VLAN_ID | 0x1000)
                msg.match = match
                msg.priority += 4
                flow_mods[receiver[0]] = msg
                log.debug('Generated flow mod for ' + dpid_to_str(receiver[0]))
                
                # Generate the actions required to strip the VLAN ID and remaining filter stages at this
                # receiver node. Note that 1 filter stage is removed by the bloom filter forwarding operation
                # if node_hop_distance[mtree_index][receiver[0]] < len(edges_to_install[mtree_index]):
                log.debug('Added bloom filter forwarding action on ' + dpid_to_str(receiver[0]))
                msg.actions.append(of.ofp_action_output(port = of.OFPP_BLOOM_PORTS))
                    
                stages_to_remove = len(edges_to_install[mtree_index]) - node_hop_distance[mtree_index][receiver[0]]
                #if stages_to_remove > 0:
                log.debug('Added pop stage header action on ' + dpid_to_str(receiver[0]) + ', stages to remove: ' + str(stages_to_remove))
                msg.actions.append(of.ofp_action_pop_shim_header(num_remove_stages = stages_to_remove))
                    
                log.debug('Added VLAN stripping action on ' + dpid_to_str(receiver[0]))
                vlan_action = of.ofp_action_pop_vlan()
                msg.actions.append(vlan_action)
                
                msg.instructions = []
                msg.instructions.append(of.ofp_instruction_actions_apply(
                                actions = msg.actions, 
                                type = 4, # OFPIT_APPLY_ACTION
                                ))
                # log.info('Egress Flow Mod Instructions: ' + str(msg.instructions))
                    
            output_port = receiver[1]
            if receiver[0] == self.src_router_dpid:
                # If the receiver is located on the root node, the output action must occur before
                # the VLAN ID and shim header are added
                log.warn('RECEIVER ON ROOT NODE')
                log.debug('Added output action on root ' + dpid_to_str(receiver[0]) + ' Port: ' + str(output_port))
                flow_mods[receiver[0]].actions.insert(0, of.ofp_action_output(port = output_port))
            else:
                # For all other nodes, the actions necessary to strip the VLAN ID and any remaining filter
                # stages were already added to the action list when the flow mod was created
                log.debug('Added output action on ' + dpid_to_str(receiver[0]) + ' Port: ' + str(output_port))
                flow_mods[receiver[0]].actions.append(of.ofp_action_output(port = output_port))
                
            log.info('Receiver ' + dpid_to_str(receiver[0]) + ' Egress Actions: ' + str(flow_mods[receiver[0]].actions))
        
        # Setup empty rules for any router not involved in this path
        for router_dpid in self.node_list:
            if not router_dpid in flow_mods and router_dpid in self.installed_node_list:
                msg = of.ofp_flow_mod()
                msg.cookie = self.flow_cookie
                match = of.ofp_match(dl_type = 0x800, nw_dst = self.dst_mcast_address, nw_src = self.src_ip)
                msg.match = match
                msg.command = of.OFPFC_DELETE
                flow_mods[router_dpid] = msg
                log.debug('Removing installed flow on ' + dpid_to_str(router_dpid))
        

        ingress_connection = core.openflow.getConnection(self.src_router_dpid)
        if ingress_connection is not None:
            # First, send the group mod message
            ingress_connection.send(group_select_msg)
            # Next, send a barrier, to ensure the group exists on the switch side before it is referenced by a flow mod
            ingress_connection.send(of.ofp_barrier_request())
        else:
            log.warn('Could not get connection for router: ' + dpid_to_str(self.src_router_dpid))
        
        # Now send all flow mods
        self.installed_node_list = []
        for router_dpid in flow_mods:
            connection = core.openflow.getConnection(router_dpid)
            if connection is not None:
                # log.info("Installing flow mod: " + str(flow_mods[router_dpid]))
                connection.send(flow_mods[router_dpid])
                if not flow_mods[router_dpid].command == of.OFPFC_DELETE:
                    self.installed_node_list.append(router_dpid)
            else:
                log.warn('Could not get connection for router: ' + dpid_to_str(router_dpid))
            
        log.info('New flows installed for Group: ' + str(self.dst_mcast_address) + ' Source: ' + str(self.src_ip) + ' FlowCookie: ' + str(self.flow_cookie))
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_flow_installation_end_time()
            core.groupflow_event_tracer.archive_trace_event(groupflow_trace_event)
            
    def install_openflow_rules_standard(self, groupflow_trace_event = None):
        """Selects routes for active receivers from the cached shortest path tree, and installs/removes OpenFlow rules using standard tree encoding.
        
        Standard tree encoding entails using a single group specific forwarding entry at every node which participates in the multicast tree.
        """
        reception_state = self.groupflow_manager.get_reception_state(self.dst_mcast_address, self.src_ip)
        log.debug('Reception state for ' + str(self.dst_mcast_address) + ': ' + str(reception_state))
        outgoing_rules = defaultdict(lambda : None)
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_route_processing_start_time(self.dst_mcast_address, self.src_ip)
        
        dst_ip_split_str = str(self.dst_mcast_address).split('.')
        dst_ip_last_octet = dst_ip_split_str[3]
        
        edges_to_install = []
        node_hop_distance = []
        calculated_path_router_dpids = []
        mtree_dst_ip = []

        for mtree_index in range(0, self.num_multi_trees):
            edges_to_install.append(defaultdict(lambda : None))
            node_hop_distance.append(defaultdict(lambda : None))
            node_hop_distance[mtree_index][self.src_router_dpid] = 0
            calculated_path_router_dpids.append([])
            mtree_dst_ip.append(IPAddr(MTREE_DST_IP_PREFIX + dst_ip_last_octet + "." + str(mtree_index + 1)))
            log.info('Using DST IP Tag: ' + str(mtree_dst_ip[0]) + ' for multi-tree #' + str(mtree_index))
        
        # First, parse the path tree maps generated by the Djikstra algorithm to
        # determine which edges should be added for each tree
        for mtree_index in range(0, self.num_multi_trees):
            log.info('Multi-tree #' + str(mtree_index) + ':')
            for receiver in reception_state:
                if receiver[0] == self.src_router_dpid:
                    continue
                if receiver[0] in calculated_path_router_dpids:
                    continue
                
                receiver_path = self.path_tree_map[mtree_index][receiver[0]]
                # log.info('Receiver path for receiver ' + str(receiver[0]) + ': ' + str(receiver_path))
                if receiver_path is None:
                    log.warn('Path could not be determined for receiver ' + dpid_to_str(receiver[0]) + ' (network is not fully connected)')
                    continue
                
                receiver_edge_list = []
                # Build the path for this particular receiver
                while receiver_path[1]:
                    receiver_edge_list.append((receiver_path[1][0], receiver_path[0]))
                    receiver_path = receiver_path[1]
                # Now that the length of the receiver path is known, install it into the dictionary of edges
                # keyed by distance from the root node
                hop_distance = 0
                receiver_edge_list.reverse()
                for edge in receiver_edge_list:
                    if edges_to_install[mtree_index][hop_distance] is None:
                        edges_to_install[mtree_index][hop_distance] = Set()
                    edges_to_install[mtree_index][hop_distance].add(edge)
                    node_hop_distance[mtree_index][edge[0]] = hop_distance
                    node_hop_distance[mtree_index][edge[1]] = hop_distance + 1
                    hop_distance += 1
                
                calculated_path_router_dpids[mtree_index].append(receiver[0])
        
        if not groupflow_trace_event is None:
            groupflow_trace_event.set_route_processing_end_time()
            groupflow_trace_event.set_flow_installation_start_time()     
        
        # Flow mod generation
        
        # flow mod 2d dictionary
        # flow_mods[mtree_index][router_dpid]
        flow_mods = defaultdict(lambda : defaultdict(lambda : None))
        
        # 1) Generate multi-tree specific flow mods for intermediate nodes
        #    in the multicast trees (i.e., those with a hop distance from
        #    the root greater than 0). These flow mods will match against the
        #    original src IP and the rewritten dst IP, and their action list
        #    will consist only of output actions to the necessary edge(s)
        for mtree_index in range(0, self.num_multi_trees):
            for hop_distance in edges_to_install[mtree_index]:
                if hop_distance == 0:
                    # First hops will be implemented in the ingress flow mod
                    continue;
                    
                for edge in edges_to_install[mtree_index][hop_distance]:
                    switch_dpid = edge[0]
                    output_port = self.groupflow_manager.adjacency[edge[0]][edge[1]]
                    
                    if flow_mods[mtree_index][switch_dpid] is None:
                        # No existing flow mod for this switch_dpid/mtree_index, generate
                        # a new one
                        msg = of.ofp_flow_mod()
                        msg.hard_timeout = 0
                        msg.idle_timeout = 0
                        msg.priority += 4
                        if switch_dpid in self.installed_node_list:
                            msg.command = of.OFPFC_MODIFY
                        else:
                            msg.command = of.OFPFC_ADD
                        match = of.ofp_match(dl_type = 0x800, nw_dst = mtree_dst_ip[mtree_index], nw_src = self.src_ip) 
                        msg.match = match
                        msg.cookie = self.flow_cookie
                        flow_mods[mtree_index][switch_dpid] = msg
                    
                    # Flow mod either already existed, or was just created. Add the
                    # output action to the necessary port to its action list
                    flow_mods[mtree_index][switch_dpid].actions.append(of.ofp_action_output(port = output_port))
                
        # 2) Generate the multi-tree specific egress flow mods. These flow mods
        #    will rewrite the packet dst IP to the original dst IP, and output
        #    the packets to the end hosts / edge networks. If a flow mod has
        #    already been generated for the switch/multi-tree pair, these
        #    actions will be appended to the action list of the existing flow
        for mtree_index in range(0, self.num_multi_trees):
            for receiver in reception_state:
                switch_dpid = receiver[0]
                
                if flow_mods[mtree_index][switch_dpid] is None:
                    # No existing flow mod for this switch_dpid/mtree_index, generate
                    # a new one
                    msg = of.ofp_flow_mod()
                    msg.hard_timeout = 0
                    msg.idle_timeout = 0
                    msg.priority += 4
                    if switch_dpid in self.installed_node_list:
                        msg.command = of.OFPFC_MODIFY
                    else:
                        msg.command = of.OFPFC_ADD
                    match = of.ofp_match(dl_type = 0x800, nw_dst = mtree_dst_ip[mtree_index], nw_src = self.src_ip) 
                    msg.match = match
                    msg.cookie = self.flow_cookie
                    flow_mods[mtree_index][switch_dpid] = msg
                
                # Flow mod either already existed, or was just created.
                # Add the flow action which rewrites the destination IP back to the original IP
                dst_ip_set_action = of.ofp_action_set_field()
                dst_ip_set_action.oxm_field = of.oxm_match_field(
                        oxm_field = of.oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IPV4_DST'],
                        oxm_length = 4,
                        data = self.dst_mcast_address.toRaw(),
                        value = self.dst_mcast_address.toStr())
                dst_ip_set_action.pack()
                flow_mods[mtree_index][switch_dpid].actions.append(dst_ip_set_action)
                
                # Add the flow action which writes the packet to the necessary output port
                output_port = receiver[1]
                flow_mods[mtree_index][switch_dpid].actions.append(of.ofp_action_output(port = output_port))
                
        # 3) Iterate through all previously generated flow mods, and fill
        #    their instructions structure with an OFPIT_APPLY_ACTION instructions
        #    using the previously generated action list
        for mtree_index in range(0, self.num_multi_trees):
            for switch_dpid in flow_mods[mtree_index]:
                flow_mods[mtree_index][switch_dpid].instructions = []
                flow_mods[mtree_index][switch_dpid].instructions.append(
                                of.ofp_instruction_actions_apply(
                                actions = flow_mods[mtree_index][switch_dpid].actions, 
                                type = 4, # OFPIT_APPLY_ACTION
                                ))
        
        # 4) Generate the ingress group mods, which use group chaining to
        #    rewrite a different dst IP for each multi-tree. A SELECT group
        #    is used to stochastically apply a different dst IP tag to
        #    each packet, and these SELECT buckets then chain to an ALL
        #    bucket to output to rewritten packets to the neccesary ports
        #    The SELECT group will have a GROUP_ID equal to the flow's cookie
        #    The ALL group for each multi-tree will have a GROUP_ID equal to
        #     (flow.cookie + mtree_index + 1)
        
        # First, generate the group mods which create the ALL groups for
        # each multi-tree. Each ALL group will have a number of buckets
        # equal to the number of output edges from the root of the tree.
        mtree_all_group_mods = []
        for mtree_index in range(0, self.num_multi_trees):
            group_msg = of.ofp_group_mod()
            group_msg.command = 0 # OFPGC_ADD
            group_msg.type = 0    # OFPGT_ALL
            group_msg.group_id = self.flow_cookie + mtree_index + 1
            
            mtree_all_group_mods.append(group_msg)
            
            # generate the bucket of actions for each output port
            for edge in edges_to_install[mtree_index][0]:
                mtree_bucket = of.ofp_bucket()
                mtree_bucket.watch_port = 0xffffffff # OFPP_ANY
                mtree_bucket.watch_group = 0xffffffff # OFPG_ANY
                bucket_actions = []
                bucket_actions.append(of.ofp_action_output(port = self.groupflow_manager.adjacency[edge[0]][edge[1]]))
                mtree_bucket.actions = bucket_actions
                mtree_all_group_mods[mtree_index].buckets.append(mtree_bucket)
        
        # Next, generate a group of type SELECT, where each select bucket consists of an
        # action rewriting the packet destination IP, and an action pointing to one of the 
        # previously generated ALL groups
        group_select_msg = of.ofp_group_mod()
        group_select_msg.command = 0   # OFPGC_ADD
        group_select_msg.type = 1      # OFPGT_SELECT
        group_select_msg.group_id = self.flow_cookie
        
        for mtree_index in range(0, self.num_multi_trees):
            mtree_bucket = of.ofp_bucket()
            mtree_bucket.weight = 10     # For now, all mtrees are given equal weight
            mtree_bucket.watch_port = 0xffffffff # OFPP_ANY
            mtree_bucket.watch_group = 0xffffffff # OFPG_ANY
            bucket_actions = []
            
            dst_ip_set_action = of.ofp_action_set_field()
            dst_ip_set_action.oxm_field = of.oxm_match_field(
                    oxm_field = of.oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IPV4_DST'],
                    oxm_length = 4,
                    data = mtree_dst_ip[mtree_index].toRaw(),
                    value = mtree_dst_ip[mtree_index].toStr())
            dst_ip_set_action.pack()
            bucket_actions.append(dst_ip_set_action)
            
            group_action = of.ofp_action_group()
            group_action.group_id = (self.flow_cookie + mtree_index + 1)
            bucket_actions.append(group_action)
            
            mtree_bucket.actions = bucket_actions
            group_select_msg.buckets.append(mtree_bucket)
        
        # 5) Finally, generate the ingress flow mod that directs incoming packets
        #    to the previously generated SELECT group
        ingress_flow_mod = of.ofp_flow_mod()
        ingress_flow_mod.hard_timeout = 0
        ingress_flow_mod.idle_timeout = 0
        ingress_flow_mod.priority += 4
        if self.src_router_dpid in self.installed_node_list:
            ingress_flow_mod.command = of.OFPFC_MODIFY
        else:
            ingress_flow_mod.command = of.OFPFC_ADD
        match = of.ofp_match(dl_type = 0x800, nw_dst = self.dst_mcast_address, nw_src = self.src_ip)
        ingress_flow_mod.match = match
        ingress_flow_mod.cookie = self.flow_cookie

        #log.debug('Generated flow mod for root node ' + dpid_to_str(self.src_router_dpid))
        # Generate the group action
        group_action = of.ofp_action_group()
        group_action.group_id = self.flow_cookie
        ingress_flow_mod.actions.append(group_action)
        ingress_flow_mod.instructions = []
        ingress_flow_mod.instructions.append(of.ofp_instruction_actions_apply(
                                actions = ingress_flow_mod.actions, 
                                type = 4, # OFPIT_APPLY_ACTION
                                ))
        
        # Group / flow mod installation
        ingress_connection = core.openflow.getConnection(self.src_router_dpid)
        if ingress_connection is not None:
            # First, send the group mod messages to install the ALL groups on the ingress router
            for mtree_index in range(0, self.num_multi_trees):
                ingress_connection.send(mtree_all_group_mods[mtree_index])
            # Next, send a barrier, to ensure the groups exist on the switch side before they are referenced by the SELECT group
            ingress_connection.send(of.ofp_barrier_request())
            # Finally, send the group mod message to install the SELECT group on the ingress router
            ingress_connection.send(group_select_msg)
        else:
            log.warn('Could not get connection for router: ' + dpid_to_str(self.src_router_dpid))
        
        # Now send all intermediate/egress flow mods
        self.installed_node_list = []
        for mtree_index in range(0, self.num_multi_trees):
            for router_dpid in flow_mods[mtree_index]:
                connection = core.openflow.getConnection(router_dpid)
                if connection is not None:
                    # log.info("Installing flow mod: " + str(flow_mods[router_dpid]))
                    connection.send(flow_mods[mtree_index][router_dpid])
                    if not flow_mods[mtree_index][router_dpid].command == of.OFPFC_DELETE:
                        self.installed_node_list.append(router_dpid)
                else:
                    log.warn('Could not get connection for router: ' + dpid_to_str(router_dpid))
        
        # Finally, send the ingress flow mod
        if ingress_connection is not None:
            ingress_connection.send(ingress_flow_mod)
        
        log.info('New flows installed for Group: ' + str(self.dst_mcast_address) + ' Source: ' + str(self.src_ip) + ' FlowCookie: ' + str(self.flow_cookie))
                
    def remove_openflow_rules(self):
        """Removes all OpenFlow rules associated with this multicast group / sender pair.

        This should be used when the group has no active receivers."""
        log.info('Removing rules on all routers for Group: ' + str(self.dst_mcast_address) + ' Source: ' + str(self.src_ip))
        for router_dpid in self.node_list:
            msg = of.ofp_flow_mod()
            msg.cookie = self.flow_cookie
            match = of.ofp_match(dl_type = 0x800, nw_dst = self.dst_mcast_address, nw_src = self.src_ip, in_port = None)
            msg.match = match
            msg.command = of.OFPFC_DELETE
            connection = core.openflow.getConnection(router_dpid)
            if connection is not None:
                connection.send(msg)
            else:
                log.warn('Could not get connection for router: ' + dpid_to_str(router_dpid))
        self.installed_node_list = []
        
        if self._flow_replacement_timer is not None:
            self._flow_replacement_timer.cancel()
            self._flow_replacement_timer = None
        
    def update_flow_placement(self, groupflow_trace_event = None):
        """Replaces the existing flows by recalculating the cached shortest path tree, and installing new OpenFlow rules."""
        self.calc_path_tree_dijkstras(groupflow_trace_event)
        self.install_openflow_rules(groupflow_trace_event)
        log.info('Replaced flows for Group: ' + str(self.dst_mcast_address) + ' Source: ' + str(self.src_ip) + ' FlowCookie: ' + str(self.flow_cookie))
    


class GroupFlowManager(EventMixin):
    """The GroupFlowManager implements multicast routing for OpenFlow networks."""
    _core_name = "openflow_groupflow"
    
    def __init__(self, link_weight_type, static_link_weight, util_link_weight, flow_replacement_mode, flow_replacement_interval, tree_encoding_mode, filter_len_iter, num_multi_trees):
        # Listen to dependencies
        def startup():
            core.openflow.addListeners(self, priority = 99)
            core.openflow_igmp_manager.addListeners(self, priority = 99)
            core.openflow_flow_tracker.addListeners(self, priority = 99)
            log.info("Startup Complete")

        self.link_weight_type = link_weight_type
        log.info('Set link weight type: ' + str(self.link_weight_type))
        self.static_link_weight = float(static_link_weight)
        if self.static_link_weight == 0:
            self.static_link_weight = sys.float_info.min
        self.util_link_weight = float(util_link_weight)
        log.info('Set StaticLinkWeight:' + str(self.static_link_weight) + ' UtilLinkWeight:' + str(self.util_link_weight))
        self.flow_replacement_mode = flow_replacement_mode
        self.flow_replacement_interval = flow_replacement_interval
        log.info('Set FlowReplacementMode:' + str(flow_replacement_mode) + ' FlowReplacementInterval:' + str(flow_replacement_interval) + ' seconds')
        
        self.filter_len_iter = filter_len_iter
        if filter_len_iter == FILTER_LEN_ITER_MINIMUM_LENGTH:
            log.info('Set FilterLengthIterationMethod: MINIMUM LENGTH')
        elif filter_len_iter == FILTER_LEN_ITER_EXPECTED_ALTERNATING:
            log.info('Set FilterLengthIterationMethod: EXPECTED ALTERNATING')
        elif filter_len_iter == FILTER_LEN_ITER_EXPECTED_LOW_FIRST:
            log.info('Set FilterLengthIterationMethod: EXPECTED LOW FIRST')
        elif filter_len_iter == FILTER_LEN_ITER_EXPECTED_HIGH_FIRST:
            log.info('Set FilterLengthIterationMethod: EXPECTED HIGH FIRST')
        self.filter_len_intervals = []
        self.precalculate_filter_len_intervals()
        log.info('Completed pre-calculation of filter length intervals')
        
        self.adjacency = defaultdict(lambda : defaultdict(lambda : None))
        self.topology_graph = []
        self.node_set = Set()
        self.multicast_paths = defaultdict(lambda : defaultdict(lambda : None))
        self.multicast_paths_by_flow_cookie = {} # Stores references to the same objects as self.multicast_paths, except this map is keyed by flow_cookie
        self._next_mcast_group_cookie = 54345;  # Arbitrary, not set to 1 to avoid conflicts with other modules
        
        # Load expected filter length array from CSV
        self.expected_filter_len_array = []
        with open("exp_filter_len.csv", "r") as f:
            self.expected_filter_len_array = [list(map(int,value)) for value in csv.reader(f, delimiter=',')]
        
        self.bloom_ids_per_router = FIXED_BIDS_PER_ROUTER
        if RANDOM_NUM_IDS_PER_ROUTER:
            self.bloom_ids_per_router = randint(RANDOM_BIDS_PER_ROUTER_MIN, RANDOM_BIDS_PER_ROUTER_MAX)
              
        # Desired reception state as delivered by the IGMP manager, keyed by the dpid of the router for which
        # the reception state applies
        self.desired_reception_state = defaultdict(lambda : None)
        
        # Set Bloom ID assignment variables
        self.next_bloom_id = 1;
        # bloom_id_map[router_dpid][port_no] -> Bloom ID assigned to port
        self.bloom_id_map = defaultdict(lambda : defaultdict(lambda : None))
        # bloom_id_adjacency[dpid1][dpid2] -> Bloom ID assigned to link from dpid1 to dpid2
        self.bloom_id_adjacency = defaultdict(lambda : defaultdict(lambda : None))
        # port_map[router_dpid][port_no] -> ofp_phy_port describing the port
        self.port_map = defaultdict(lambda : defaultdict(lambda : None))
        
        self.tree_encoding_mode = tree_encoding_mode
        if self.tree_encoding_mode == TREE_ENCODING_STANDARD:
            log.info('Set Tree Encoding Mode: STANDARD')
        elif self.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            log.info('Set Tree Encoding Mode: BLOOM FILTER')
            
        self.num_multi_trees = num_multi_trees
        log.info('Num Multi Trees: ' + str(self.num_multi_trees))
        
        # Setup listeners
        core.call_when_ready(startup, ('openflow', 'openflow_igmp_manager', 'openflow_flow_tracker'))
    
    def get_new_mcast_group_cookie(self):
        """Returns a new, unique cookie which should be assigned to a multicast_group / sender pair.

        Using a unique cookie per multicast group / sender allows the FlowTracker module to accurately track
        bandwidth utilization on a per-flow basis.
        """
        self._next_mcast_group_cookie += (self.num_multi_trees + 1)
        log.debug('Generated new flow cookie: ' + str(self._next_mcast_group_cookie - (self.num_multi_trees + 1)))
        return self._next_mcast_group_cookie - (self.num_multi_trees + 1)
    
    def get_reception_state(self, mcast_group, src_ip):
        """Returns locations to which traffic must be routed for the specified multicast address and sender IP.

        Returns a list of tuples of the form (router_dpid, output_port).
        """
        # log.debug('Calculating reception state for mcast group: ' + str(mcast_group) + ' Source: ' + str(src_ip))
        reception_state = []
        for router_dpid in self.desired_reception_state:
            # log.debug('Considering router: ' + dpid_to_str(router_dpid))
            if mcast_group in self.desired_reception_state[router_dpid]:
                for port in self.desired_reception_state[router_dpid][mcast_group]:
                    if not self.desired_reception_state[router_dpid][mcast_group][port]:
                        reception_state.append((router_dpid, port))
                        # log.debug('Reception from all sources desired on port: ' + str(port))
                    elif src_ip in self.desired_reception_state[router_dpid][mcast_group][port]:
                        reception_state.append((router_dpid, port))
                        # log.debug('Reception from specific source desired on port: ' + str(port))
        else:
            return reception_state
    
    def get_edges_to_exclude(self, edge_set):
        """Given a set of edges, returns other edges which egress from the tail nodes of the original edge list"""
        exclude_edges = Set()
        for edge in edge_set:
            if self.adjacency[edge[1]] is not None:
                for egress_node in self.adjacency[edge[1]]:
                    exclude_edges.add((edge[1], egress_node))
        
        return exclude_edges
    
    def get_tree_root_node(self, edge_list):
        """Accepts a list of edges defining a tree, and returns the root node of the tree"""
        incoming_edge_dict = defaultdict(lambda : None)
        for edge in edge_list:
            if incoming_edge_dict[edge[0]] is None:
                incoming_edge_dict[edge[0]] = 0
            if incoming_edge_dict[edge[1]] is None:
                incoming_edge_dict[edge[1]] = 0
            incoming_edge_dict[edge[1]] += 1
            
        for node in incoming_edge_dict.iterkeys():
            if incoming_edge_dict[node] == 0:
                return node
                
        return None

    def get_edges_by_hop_distance(self, root_node, max_hops):
        """Returns a set of edges in the network, indexed by their distance from a specific root node.
        
        Edges are returned as tuples of <egress_router_dpid, ingress_router_dpid>. Tuples are returned as sets which 
        are contained in a list, which is keyed by the hop distance from the specified root node (starting at 0, 
        which are the edges directly connected to the root node. The max_hops parameter specifies the maximum hop 
        distance which should be considered.
        """
        edge_list = []
        for hop_distance in range(0, max_hops):
            if hop_distance == 0:
                edge_list.append(Set())
                for edge in self.topology_graph:
                    if edge[0] == root_node:
                        edge_list[0].add(edge)
            else:
                edge_list.append(Set())
                for edge1 in edge_list[hop_distance - 1]:
                    root_node = edge1[1]
                    for edge2 in self.topology_graph:
                        if edge2[1] == edge1[0]:
                            continue
                        if edge2[0] == root_node:
                            edge_list[hop_distance].add(edge2)
        
        return edge_list

    def drop_packet(self, packet_in_event):
        """Drops the packet represented by the PacketInEvent without any flow table modification"""
        msg = of.ofp_packet_out()
        msg.data = packet_in_event.ofp
        msg.buffer_id = packet_in_event.ofp.buffer_id
        msg.in_port = packet_in_event.port
        msg.actions = []    # No actions = drop packet
        packet_in_event.connection.send(msg)

    def get_topo_debug_str(self):
        debug_str = '\n===== GroupFlow Learned Topology'
        for edge in self.topology_graph:
            debug_str += '\n(' + dpid_to_str(edge[0]) + ',' + dpid_to_str(edge[1]) + ')'
        return debug_str + '\n===== GroupFlow Learned Topology'
        
    def parse_topology_graph(self, adjacency_map):
        """Parses an adjacency map into a node and edge graph (which is cached in self.topology_graph and self.node_set)."""
        new_topo_graph = []
        new_node_list = []
        for router1 in adjacency_map:
            for router2 in adjacency_map[router1]:
                if self.port_map[router1] is not None and self.port_map[router1][adjacency_map[router1][router2]] is not None:
                    # Assign a bloom ID to the port if a port descriptor is available
                    self.assign_bloom_id(router1, adjacency_map[router1][router2])
                new_topo_graph.append((router1, router2))
                if not router2 in new_node_list:
                    new_node_list.append(router2)
            if not router1 in new_node_list:
                new_node_list.append(router1)
        self.topology_graph = new_topo_graph
        self.node_set = Set(new_node_list)
    
    def _handle_PacketIn(self, event):
        """Processes PacketIn events to detect multicast sender IPs."""
        #log.info('_handle_PacketIn called')
        router_dpid = event.connection.dpid
        if not router_dpid in self.node_set:
            log.info('Got packet from unrecognized router.')
            return  # Ignore packets from unrecognized routers
            
        igmp_pkt = event.parsed.find(pkt.igmpv3)
        if not igmp_pkt is None:
            return # IGMP packets should be ignored by this module
            
        ipv4_pkt = event.parsed.find(pkt.ipv4)
        if not ipv4_pkt is None:
            # ==== IPv4 Packet ====
            # Check the destination address to see if this is a multicast packet
            # log.info('Got IPv4 packet from Switch: ' + dpid_to_str(event.dpid) + ' - Port: ' + str(event.port))
            if ipv4_pkt.dstip.inNetwork('224.0.0.0/4'):
                log.info('Got multicast packet from Switch: ' + dpid_to_str(event.dpid) + ' - Port: ' + str(event.port) + ' - Src IP: ' + str(ipv4_pkt.srcip) + ' - Dst IP: ' + str(ipv4_pkt.dstip))
                # Ignore multicast packets from adjacent routers
                for router_dpid2 in self.adjacency[router_dpid]:
                    if self.adjacency[router_dpid][router_dpid2] == event.port:
                        return
                        
                group_reception = self.get_reception_state(ipv4_pkt.dstip, ipv4_pkt.srcip)
                if group_reception:
                    if not self.multicast_paths[ipv4_pkt.dstip][ipv4_pkt.srcip] is None:
                        log.debug('Got multicast packet from source which should already be configured Router: ' + dpid_to_str(event.dpid) + ' Port: ' + str(event.port))
                        if ENABLE_OUT_OF_ORDER_PACKET_DELIVERY:
                            # This may cause OFPBRC_BUFFER_UNKNOWN errors if the controller takes too long to respond
                            # Send the packet back to the switch for forwarding
                            msg = of.ofp_packet_out()
                            msg.data = event.ofp
                            msg.buffer_id = event.ofp.buffer_id
                            msg.in_port = event.port
                            msg.actions = [of.ofp_action_output(port = of.OFPP_TABLE)]
                            event.connection.send(msg)
                        return
                        
                    log.info('Got multicast packet from new source. Router: ' + dpid_to_str(event.dpid) + ' Port: ' + str(event.port))
                    log.debug('Reception state for this group:')
                    
                    for receiver in group_reception:
                        log.debug('Multicast Receiver: ' + dpid_to_str(receiver[0]) + ':' + str(receiver[1]))

                    groupflow_trace_event = None
                    try:
                        groupflow_trace_event = core.groupflow_event_tracer.init_groupflow_event_trace()
                    except:
                        pass
                    path_setup = MulticastPath(ipv4_pkt.srcip, router_dpid, event.port, ipv4_pkt.dstip, self, groupflow_trace_event)
                    self.multicast_paths[ipv4_pkt.dstip][ipv4_pkt.srcip] = path_setup
                    self.multicast_paths_by_flow_cookie[path_setup.flow_cookie] = path_setup
                    path_setup.install_openflow_rules(groupflow_trace_event)
    
    def _handle_MulticastGroupEvent(self, event):
        """Processes MulticastGroupEvents (generated by the IGMPManager module) and adjusts routing as necessary to fulfill desired reception state"""
        log.info(event.debug_str())
        # Save a copy of the old reception state to account for members which left a group
        old_reception_state = None
        if event.router_dpid in self.desired_reception_state:
            old_reception_state = self.desired_reception_state[event.router_dpid]
        
        # Set the new reception state
        self.desired_reception_state[event.router_dpid] = event.desired_reception
        log.info('Set new reception state for router: ' + dpid_to_str(event.router_dpid))
        
        # Build a list of all multicast groups that may be impacted by this change
        mcast_addr_list = []
        removed_mcast_addr_list = []
        for multicast_addr in self.desired_reception_state[event.router_dpid]:
            mcast_addr_list.append(multicast_addr)
            
        if not old_reception_state is None:
            for multicast_addr in old_reception_state:
                # Capture groups which were removed in this event
                if not multicast_addr in mcast_addr_list:
                    log.info('Multicast group ' + str(multicast_addr) + ' no longer requires reception')
                    removed_mcast_addr_list.append(multicast_addr)
                elif multicast_addr in self.desired_reception_state[event.router_dpid] \
                        and set(old_reception_state[multicast_addr]) == set(self.desired_reception_state[event.router_dpid][multicast_addr]):
                    # Prevent processing of groups that did not change
                    mcast_addr_list.remove(multicast_addr)
                    log.debug('Prevented redundant processing of group: ' + str(multicast_addr))
        
        # Rebuild multicast trees for relevant multicast groups
        log.debug('Recalculating paths due to new reception state change')
        for multicast_addr in mcast_addr_list:
            if multicast_addr in self.multicast_paths:
                log.debug('Recalculating paths for group ' + str(multicast_addr))
                groupflow_trace_event = None
                try:
                    groupflow_trace_event = core.groupflow_event_tracer.init_groupflow_event_trace(event.igmp_trace_event)
                except:
                    pass
                for source in self.multicast_paths[multicast_addr]:
                    log.info('Recalculating paths for group ' + str(multicast_addr) + ' Source: ' + str(source))
                    self.multicast_paths[multicast_addr][source].install_openflow_rules(groupflow_trace_event)
            else:
                log.debug('No existing sources for group ' + str(multicast_addr))
                
        for multicast_addr in removed_mcast_addr_list:
            if multicast_addr in self.multicast_paths:
                sources_to_remove = []
                for source in self.multicast_paths[multicast_addr]:
                    log.info('Removing flows for group ' + str(multicast_addr) + ' Source: ' + str(source))
                    self.multicast_paths[multicast_addr][source].remove_openflow_rules()
                    del self.multicast_paths_by_flow_cookie[self.multicast_paths[multicast_addr][source].flow_cookie]
                    sources_to_remove.append(source)
                    
                for source in sources_to_remove:
                    del self.multicast_paths[multicast_addr][source]
            else:
                log.info('Removed multicast group ' + str(multicast_addr) + ' has no known paths')
    
    def _handle_MulticastTopoEvent(self, event):
        """Processes MulticastTopoEvents (generated by the IGMPManager module) and adjusts routing as necessary to account for topology changes
        
        Note: In the current implementation, this recalculates all multicast routes.
        """
        # log.info(event.debug_str())
        self.adjacency = event.adjacency_map
        self.parse_topology_graph(event.adjacency_map)
        # log.info(self.get_topo_debug_str())
        
        if self.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            # Assign bloom identifiers to any pair of ports which came up in this event
            if event.event_type == MulticastTopoEvent.LINK_UP:
                for link in event.link_changes:
                    log.info("Assigning new bloom id for Switch: " + str(link[0]) + ' - Port: ' + str(link[2]))
                    self.assign_bloom_id(link[0], link[2])
                
        if self.multicast_paths:
            log.warn('Multicast topology changed, recalculating all paths.')
            for multicast_addr in self.multicast_paths:
                for source in self.multicast_paths[multicast_addr]:
                    groupflow_trace_event = None
                    try:
                        groupflow_trace_event = core.groupflow_event_tracer.init_groupflow_event_trace()
                    except:
                        pass
                    self.multicast_paths[multicast_addr][source].update_flow_placement(groupflow_trace_event)
    
    def _handle_LinkUtilizationEvent(self, event):
        """Processes LinkUtilizationEvents (generated by the FlowTracker module), and replaces flows that traverse the specified link"""
        
        if event.link_utilization >= core.openflow_flow_tracker.link_max_bw:
            log.debug('Link Fully Utilized! Switch:' + dpid_to_str(event.router_dpid) + ' Port:' + str(event.output_port))
        
        # Ignore the event if congestion threshold based flow replacement is not enabled
        if self.flow_replacement_mode != CONG_THRESHOLD_FLOW_REPLACEMENT:
            return
            
        log.debug('Got LinkUtilEvent - Switch: ' + dpid_to_str(event.router_dpid) + ' Port: ' + str(event.output_port) + '\n\tUtil: ' + str(event.link_utilization))
            
        replacement_time = time.time()
        
        # 1) Determine the amount of utilization that should be replaced to bring the link back under the congestion threshold
        replacement_utilization = event.link_utilization - event.cong_threshold
        if replacement_utilization < 0:
            log.warn('LinkUtilizationEvent specified negative replacement utilization.')
            return
        log.debug('Attempting replacement of ' + str(replacement_utilization) + ' Mbps of flows')
        
        # 2) Build a list of the flows managed by this module that are contributing to congestion, sorted by decreasing utilization
        replacement_flows = []
        for event_flow_cookie in event.flow_map:
            if event_flow_cookie in self.multicast_paths_by_flow_cookie:
                replacement_flows.append((event_flow_cookie, event.flow_map[event_flow_cookie]))
        replacement_flows.sort(key = lambda flow: flow[1])
        log.debug('Candidates for flow replacement: ' + str(replacement_flows))
        
        # 3) Replace flows until all candidates have been processed, or the targeted replacement utilization is reached
        # Note that flows which have been recently replaced will not be replaced again
        replaced_utilization = 0
        for flow in replacement_flows:
            log.debug('FlowCookie: ' + str(flow[0]) + ' CurrentTime: ' + str(replacement_time) + ' LastReplacementTime: ' + str(self.multicast_paths_by_flow_cookie[flow[0]]._last_flow_replacement_time))
            if self.multicast_paths_by_flow_cookie[flow[0]]._last_flow_replacement_time is not None:
                log.debug('Replacement Interval: ' + str(self.multicast_paths_by_flow_cookie[flow[0]]._last_flow_replacement_time))
                
            if (self.multicast_paths_by_flow_cookie[flow[0]]._last_flow_replacement_time is None) or (
                    replacement_time - self.multicast_paths_by_flow_cookie[flow[0]]._last_flow_replacement_time >= self.flow_replacement_interval):
                log.debug('Replacing multicast flow with cookie: ' + str(flow[0]) + ' Bitrate: ' + str(flow[1]) + ' Mbps')
                self.multicast_paths_by_flow_cookie[flow[0]].update_flow_placement()
            
                replaced_utilization += flow[1]
                # Note: This causes the replacement to stop after replacing a single flow (may help prevent thrashing)
                # Uncomment this to have the module replace flows until the current link utilization minus the replacement bandwidth 
                # is less than the link's congestion threshold.
                break
            
            # Note: Flows which are not actually replaced are counted toward the replacement utilization here, as it assumed that these flows
            # are already in the process of being replaced (this assumption should hold valid as long as the flow replacement interval is not
            # greater than 3 sampling intervals of the flow tracker)
            if replaced_utilization >= replacement_utilization:
                break
        
        log.debug('Replaced ' + str(replaced_utilization) + ' Mbps of flows')

    def assign_bloom_id(self, router_dpid, port_no):
        """Assigns the next unused bloom identifier to the specified port, and enables bloom filter forwarding on the port."""
        if self.port_map[router_dpid] is None or self.port_map[router_dpid][port_no] is None:
            log.warn('ERROR: Attempted to assign bloom ID to port for which no port descriptor has been received.')
            return
        
        bloom_id = 0
        #if (self.port_map[router_dpid][port_no].config & of.OFPPC_NO_BLOOM_FWD) > 0:  
        
        msg = of.ofp_port_mod()
        msg.port_no = port_no
        if self.bloom_id_map[router_dpid][port_no] is None:
            if FIXED_BLOOM_IDS:
                msg.bloom_id = (router_dpid * self.bloom_ids_per_router) + port_no
            else:
                msg.bloom_id = self.next_bloom_id
            self.bloom_id_map[router_dpid][port_no] = msg.bloom_id
            self.next_bloom_id = self.next_bloom_id + 1
        else:
            msg.bloom_id = self.bloom_id_map[router_dpid][port_no]
        bloom_id = msg.bloom_id
        msg.hw_addr = self.port_map[router_dpid][port_no].hw_addr
        msg.mask |= of.OFPPC_NO_BLOOM_FWD
        connection = core.openflow.getConnection(router_dpid)
        if connection is not None:
            connection.send(msg)
            self.port_map[router_dpid][port_no].config &= 127 # Not(of.OFPPC_NO_BLOOM_FWD)
            # log.info('Assigned Bloom ID ' + str(msg.bloom_id) + ' to ' + dpid_to_str(router_dpid) + ':' + str(port_no))
        else:
            log.warn('Could not get connection for router: ' + dpid_to_str(router_dpid))
                
        #else:
        #    bloom_id = self.bloom_id_map[router_dpid][port_no]
            
        # Record the bloom id assigned to this port to the adjacency map, if it has not
        # already been recorded
        if self.adjacency[router_dpid] is None:
            return
        else:
            for dpid2 in self.adjacency[router_dpid]:
                if self.adjacency[router_dpid][dpid2] is not None and self.adjacency[router_dpid][dpid2] == port_no:
                    if self.bloom_id_adjacency[router_dpid][dpid2] is not None:
                        break
                    self.bloom_id_adjacency[router_dpid][dpid2] = bloom_id
                    log.debug('Recorded bloom ID: ' + str(bloom_id) + ' for edge ' + dpid_to_str(router_dpid) + ' -> ' + dpid_to_str(dpid2))
                    break
        
        
    def _handle_MPPortDescMultipartReceived(self, event):
        """Assigns the next available bloom identifier to new ports as they are reported to the controller"""
        log.info("Handling MPPortDescMultipart for Switch: " + dpid_to_str(event.dpid))
        if self.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            for port in event.ofp[0].body:
                if port.port_no != of.OFPP_CONTROLLER and port.port_no != of.OFPP_LOCAL:
                    # Store the port descriptor associated with this event
                    if self.port_map[event.dpid] is None:
                        self.port_map[event.dpid] = defaultdict(lambda : None)
                    self.port_map[event.dpid][port.port_no] = port
                    
                    # Assign a bloom ID to the port if it has been detected as an adjacency to another switch
                    if self.adjacency[event.dpid] is not None:
                        for dpid2 in self.adjacency[event.dpid]:
                            if self.adjacency[event.dpid][dpid2] == port.port_no:
                                self.assign_bloom_id(event.dpid, port.port_no)
                            
    def _handle_PortStatus(self, event):
        """Assigns the next available bloom identifier to new ports as they are reported to the controller"""
        #self.bloom_id_map[router_dpid1][router_dpid2] = self.next_bloom_id;
        log.warn("DEPRECATED MESSAGE: Handling PortStatus for Switch: " + dpid_to_str(event.dpid) + " - Port: " + str(event.port))
        if self.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            if event.port != of.OFPP_CONTROLLER and event.port != of.OFPP_LOCAL and event.modified or event.added:
                # Store the port descriptor associated with this event
                if self.port_map[event.dpid] is None:
                    self.port_map[event.dpid] = defaultdict(lambda : None)
                self.port_map[event.dpid][event.port] = event.ofp.desc
                
                # Assign a bloom ID to the port if it has been detected as an adjacency to another switch
                if self.adjacency[event.dpid] is not None:
                    for dpid2 in self.adjacency[event.dpid]:
                        if self.adjacency[event.dpid][dpid2] == event.port:
                            self.assign_bloom_id(event.dpid, event.port)
    
    def _handle_FeaturesReceived(self, event):
        """Assigns bloom ids to ports which are present in the initial connection handshake, and installs the semi-permanent bloom filter forwarding rule"""
        log.info("Handling FeaturesReceived for Switch: " + dpid_to_str(event.dpid))
        if self.tree_encoding_mode == TREE_ENCODING_BLOOM_FILTER:
            for port in event.ofp.ports:
                if port.port_no == of.OFPP_CONTROLLER or port.port_no == of.OFPP_LOCAL:
                    continue
                # Store the port descriptor associated with this event
                if self.port_map[event.dpid] is None:
                    self.port_map[event.dpid] = defaultdict(lambda : None)
                self.port_map[event.dpid][port.port_no] = port
                
                # Assign a bloom ID to the port if it has been detected as an adjacency to another switch
                if self.adjacency[event.dpid] is not None:
                    for dpid2 in self.adjacency[event.dpid]:
                        if self.adjacency[event.dpid][dpid2] == port.port_no:
                            self.assign_bloom_id(event.dpid, port.port_no)
            
            msg = of.ofp_flow_mod()
            msg.hard_timeout = 0
            msg.idle_timeout = 0
            msg.command = of.OFPFC_ADD
            match = of.ofp_match(dl_type = 0x0800, dl_vlan = BLOOMFLOW_RESERVED_VLAN_ID | 0x1000)
            msg.match = match
            msg.priority += 3
            msg.cookie = BLOOMFLOW_RESERVED_VLAN_ID
            msg.actions.append(of.ofp_action_output(port = of.OFPP_BLOOM_PORTS))
            event.connection.send(msg)
            log.info('Installed bloom filter forwarding rule on ' + dpid_to_str(event.dpid))
    
    def expected_filter_len(self, alpha, beta):
        # Fetches the expected filter length for a given alpha/beta from
        # a previously calculated array loaded from CSV
        return self.expected_filter_len_array[alpha][beta]
        
    def precalculate_filter_len_intervals(self):
        # Pre-calculates and caches all possible filter length intervals for
        # the configured filter length iteration method and MAX_FILTER_LEN_BITS
        self.filter_len_intervals = []
        
        # Expected filter length of 0 should not produce a valid filter length interval,
        # therefore the first entry in the filter_len_intervals list (with index 0) is
        # set to an empty list
        self.filter_len_intervals.append([])
        
        for expected_fpf_len in range(1, MAX_FILTER_LEN_BITS + 1):
            if self.filter_len_iter == FILTER_LEN_ITER_MINIMUM_LENGTH:
                self.filter_len_intervals.append(range(MIN_FILTER_LEN_BITS, MAX_FILTER_LEN_BITS + 1))
            elif self.filter_len_iter == FILTER_LEN_ITER_EXPECTED_LOW_FIRST:
                filter_len_test_range = range(expected_fpf_len, MIN_FILTER_LEN_BITS - 1, -1)
                filter_len_test_range = filter_len_test_range + range(expected_fpf_len + 1, MAX_FILTER_LEN_BITS + 1)
                self.filter_len_intervals.append(filter_len_test_range)
            elif self.filter_len_iter == FILTER_LEN_ITER_EXPECTED_HIGH_FIRST:
                filter_len_test_range = range(expected_fpf_len, MAX_FILTER_LEN_BITS + 1)
                filter_len_test_range = filter_len_test_range + range(expected_fpf_len - 1, MIN_FILTER_LEN_BITS - 1, -1)
                self.filter_len_intervals.append(filter_len_test_range)
            elif self.filter_len_iter == FILTER_LEN_ITER_EXPECTED_ALTERNATING:
                low_list = range(expected_fpf_len - 1, MIN_FILTER_LEN_BITS - 1, -1)
                high_list = range(expected_fpf_len, MAX_FILTER_LEN_BITS + 1)
                filter_len_test_range = [x for x in itertools.chain.from_iterable(itertools.izip_longest(high_list, low_list)) if x]
                self.filter_len_intervals.append(filter_len_test_range)
        
    
    def get_filter_len_interval(self, expected_fpf_len):
        # Fetches the filter length interval for the configured filter length iteration
        # method and expected false-positive-free filter length previously
        # calculated and cached by precalculate_filter_len_intervals()
        return self.filter_len_intervals[expected_fpf_len]

def launch(link_weight_type = 'linear', static_link_weight = STATIC_LINK_WEIGHT, util_link_weight = UTILIZATION_LINK_WEIGHT, 
        flow_replacement_mode = 'none', flow_replacement_interval = FLOW_REPLACEMENT_INTERVAL_SECONDS, 
        tree_encoding_mode = TREE_ENCODING_STANDARD, filter_len_iter = FILTER_LEN_ITER_DEFAULT, num_multi_trees = 1):
    # Method called by the POX core when launching the module
    link_weight_type_enum = LINK_WEIGHT_LINEAR   # Default
    if 'linear' in str(link_weight_type):
        link_weight_type_enum = LINK_WEIGHT_LINEAR
    elif 'exponential' in str(link_weight_type):
        link_weight_type_enum = LINK_WEIGHT_EXPONENTIAL
    
    flow_replacement_mode_int = NO_FLOW_REPLACEMENT
    if 'periodic' in str(flow_replacement_mode):
        flow_replacement_mode_int = PERIODIC_FLOW_REPLACEMENT
    if 'cong_threshold' in str(flow_replacement_mode):
        flow_replacement_mode_int = CONG_THRESHOLD_FLOW_REPLACEMENT
    
    if 'standard' in str(tree_encoding_mode):
        tree_encoding_mode = TREE_ENCODING_STANDARD
    if 'bloom_filter' in str(tree_encoding_mode):
        tree_encoding_mode = TREE_ENCODING_BLOOM_FILTER
        
    if 'minimum_length' in str(filter_len_iter):
        filter_len_iter = FILTER_LEN_ITER_MINIMUM_LENGTH
    elif 'expected_alternating' in str(filter_len_iter):
        filter_len_iter = FILTER_LEN_ITER_EXPECTED_ALTERNATING
    elif 'expected_low_first' in str(filter_len_iter):
        filter_len_iter = FILTER_LEN_ITER_EXPECTED_LOW_FIRST
    elif 'expected_high_first' in str(filter_len_iter):
        filter_len_iter = FILTER_LEN_ITER_EXPECTED_HIGH_FIRST
    else:
        filter_len_iter = FILTER_LEN_ITER_DEFAULT
        
    groupflow_manager = GroupFlowManager(link_weight_type_enum, float(static_link_weight), float(util_link_weight), flow_replacement_mode_int,
        float(flow_replacement_interval), int(tree_encoding_mode), int(filter_len_iter), int(num_multi_trees))
    core.register('openflow_groupflow', groupflow_manager)