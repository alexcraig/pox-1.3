# Copyright 2011-2012 James McCauley
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
An L2 learning switch.

It is derived from one written live for an SDN crash course.
It is somwhat similar to NOX's pyswitch in that it installs
exact-match rules for each flow.
"""

from pox.core import core
import pox.openflow.libopenflow_04 as of
from pox.lib.util import dpid_to_str
from pox.lib.util import str_to_bool
import time

import pickle

log = core.getLogger()

# We don't want to flood immediately when a switch connects.
# Can be overriden on commandline.
_flood_delay = 0

class LearningSwitch (object):
  """
  The learning switch "brain" associated with a single OpenFlow switch.

  When we see a packet, we'd like to output it on a port which will
  eventually lead to the destination.  To accomplish this, we build a
  table that maps addresses to ports.

  We populate the table by observing traffic.  When we see a packet
  from some source coming from some port, we know that source is out
  that port.

  When we want to forward traffic, we look up the desintation in our
  table.  If we don't know the port, we simply send the message out
  all ports except the one it came in on.  (In the presence of loops,
  this is bad!).

  In short, our algorithm looks like this:

  For each packet from the switch:
  1) Use source address and switch port to update address/port table
  2) Is transparent = False and either Ethertype is LLDP or the packet's
     destination address is a Bridge Filtered address?
     Yes:
        2a) Drop packet -- don't forward link-local traffic (LLDP, 802.1x)
            DONE
  3) Is destination multicast?
     Yes:
        3a) Flood the packet
            DONE
  4) Port for destination address in our address/port table?
     No:
        4a) Flood the packet
            DONE
  5) Is output port the same as input port?
     Yes:
        5a) Drop packet and similar ones for a while
  6) Install flow table entry in the switch so that this
     flow goes out the appopriate port
     6a) Send the packet out appropriate port
  """
  def __init__ (self, connection, transparent):
    # Switch we'll be adding L2 learning switch capabilities to
    self.connection = connection
    self.transparent = transparent

    # Our table
    self.macToPort = {}

    # We want to hear PacketIn messages, so we listen to the connection
    connection.addListeners(self)

    # We just use this to know when to log a helpful message
    self.hold_down_expired = _flood_delay == 0

    #log.debug("Initializing LearningSwitch, transparent=%s",  str(self.transparent))


  # Handle packet in messages from the switch to implement above algorithm.
  def _handle_PacketIn (self, event):

    packet = event.parsed

    #MyEncoder().encode(packet)

    #data_string = pickle.dumps(packet)
    #log.debug('PACKET object structure: %s', data_string)

    #log.debug(json.dumps(packet, default=lambda o: o.__dict__, sort_keys=True, indent=4))
    log.debug(packet._to_str())

    # test - hub behaviour
    """
    msg = of.ofp_packet_out()
    msg.data = event.ofp
    msg.actions.append(of.ofp_action_output(port = of.OFPP_FLOOD))
    event.connection.send(msg)
    """

    # Floods the packet
    def flood (message = None):
      msg = of.ofp_packet_out()
      if time.time() - self.connection.connect_time >= _flood_delay:
        # Only flood if we've been connected for a little while...

        if self.hold_down_expired is False:
          # Oh yes it is!
          self.hold_down_expired = True
          log.info("%s: Flood hold-down expired -- flooding", dpid_to_str(event.dpid))

        if message is not None: log.debug(message)
        #log.debug("%i: flood %s -> %s", event.dpid,packet.src,packet.dst)
        # OFPP_FLOOD is optional; on some switches you may need to change
        # this to OFPP_ALL.
        msg.actions.append(of.ofp_action_output(port = of.OFPP_FLOOD))

      else:
        pass
        #log.info("Holding down flood for %s", dpid_to_str(event.dpid))
      msg.data = event.ofp
      msg.in_port = event.port
      self.connection.send(msg)

    def drop (duration = None):
      """
      Drops this packet and optionally installs a flow to continue
      dropping similar ones for a while
      """
      if duration is not None:
        if not isinstance(duration, tuple):
          duration = (duration,duration)


        #action = of.ofp_action_output(port = of.OFPP_FLOOD, # TODO other port? 
        #                              max_len = of.OFPCML_NO_BUFFER)
        #msg = of.ofp_flow_mod(actions=[action],
        #                      match = of.ofp_match.from_packet(packet),
        #                      idle_timeout = duration[0],
        #                      hard_timeout = duration[1],
        #                      buffer_id = event.ofp.buffer_id,
        #                      )
        #self.connection.send(msg)
        
      elif event.ofp.buffer_id is not None:
        msg = of.ofp_packet_out()
        msg.buffer_id = event.ofp.buffer_id
        msg.in_port = event.port
        self.connection.send(msg)
    
    # 1
    self.macToPort[packet.src] = event.port 

    # 2
    if not self.transparent: 
      if packet.type == packet.LLDP_TYPE or packet.dst.isBridgeFiltered():
        drop() # 2a
        return

    # 3 - multicast - let's flood 
    if packet.dst.is_multicast:
      #log.info("Multicast - flooding")
      # 3a
      flood() 

    elif packet.dst.toRaw() == (b'\xff' * 6):
      #log.info("Broadcast - flooding")
      flood()
    
    # no multicast - let's examine the packet further
    else:
      # 4 - not yet have port-mac association - let's flood
      if packet.dst not in self.macToPort:
        flood("Port for %s unknown -- flooding" % (packet.dst,)) # 4a
      
      # we have mac associated with port
      else:
        port = self.macToPort[packet.dst]
        log.debug("we have mac associated with port %s", of.ofp_port_map.get(port, str(port)))

        # 5 - packet port the same as the (what entity is self???) port 
        if port == event.port: # 5
          # 5a
          log.info("Same port for packet from %s -> %s on %s.%s.  Drop."  % (packet.src, 
                                                                             packet.dst,
                                                                             dpid_to_str(event.dpid), 
                                                                             of.ofp_port_map.get(port, str(port)),
                                                                             ))

          #log.debug(" port %s event.port %s", hex(port), hex(event.port))

          drop(10)
          return
       
        # 6 - let's install proper flow matching rule
        log.debug("installing flow for %s.%i -> %s.%s" % (packet.src, 
                                                          event.port, 
                                                          packet.dst, 
                                                          of.ofp_port_map.get(port, str(port)),
                                                          ))
        
        # 6a
        msg = of.ofp_flow_mod(match = of.ofp_match.from_packet(packet,      # ofp_packet_in instance
                                                               event.port,  # in port
                                                               False,       # spec_frags 
                                                               True,        # l2_only - new feature switching between L2 matches and L2-4 matches
                                                               ),
                              idle_timeout = 10,
                              hard_timeout = 30,
                              actions = [of.ofp_action_output(port = port)],
                              data = event.ofp 
                              )

        self.connection.send(msg)


class l2_learning (object):
  """
  Waits for OpenFlow switches to connect and makes them learning switches.
  """
  def __init__ (self, transparent):
    core.openflow.addListeners(self)
    self.transparent = transparent

  def _handle_ConnectionUp (self, event):
    log.debug("Connection %s" % (event.connection,))
    LearningSwitch(event.connection, self.transparent)


def launch (transparent=False, hold_down=_flood_delay):
  """
  Starts an L2 learning switch.
  """
  try:
    global _flood_delay
    _flood_delay = int(str(hold_down), 10)
    assert _flood_delay >= 0
  except:
    raise RuntimeError("Expected hold-down to be a number")

  core.registerNew(l2_learning, str_to_bool(transparent))
