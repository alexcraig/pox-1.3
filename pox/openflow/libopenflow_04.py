# Copyright 2011,2012 James McCauley 2013 Viktor Sulak
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

from __future__ import print_function

import struct
import operator
from itertools import chain, repeat
import sys
from pox.core import core

from pox.lib.packet.packet_base import packet_base
from pox.lib.packet.ethernet import ethernet
from pox.lib.packet.vlan import vlan
from pox.lib.packet.llc import llc
from pox.lib.packet.ipv4 import ipv4
from pox.lib.packet.udp import udp
from pox.lib.packet.tcp import tcp
from pox.lib.packet.icmp import icmp
from pox.lib.packet.arp import arp

from pox.lib.addresses import *
from pox.lib.util import assert_type
from pox.lib.util import initHelper
from pox.lib.util import hexdump
from pox.lib.util import is_listlike

#from pox.openflow import oxm_fields
import binascii

EMPTY_ETH = EthAddr(None)

log = core.getLogger()

# ----------------------------------------------------------------------
# Logging
# ----------------------------------------------------------------------

_logger = None
def _log (debug=None, info=None, warn=None, error=None):
  if not _logger: return
  if debug: _logger.debug(debug)
  if info: _logger.info(info)
  if warn: _logger.warn(warn)
  if error: _logger.error(error)

# ----------------------------------------------------------------------

# ----------------------------------------------------------------------
# XID Management
# ----------------------------------------------------------------------

MAX_XID = 0x7fFFffFF


def XIDGenerator (start = 1, stop = MAX_XID):
  i = start
  while True:
    yield i
    i += 1
    if i > stop:
      i = start

def xid_generator (start = 1, stop = MAX_XID):
  return XIDGenerator(start, stop).next

def user_xid_generator ():
  return xid_generator(0x80000000, 0xffFFffFF)

generate_xid = xid_generator()

# ----------------------------------------------------------------------


# ----------------------------------------------------------------------
# Packing / Unpacking
# ----------------------------------------------------------------------

_PAD = b'\x00'
_PAD2 = _PAD*2
_PAD3 = _PAD*3
_PAD4 = _PAD*4
_PAD6 = _PAD*6

# Raised when one tries to unpack more data than is available
class UnderrunError (RuntimeError):
  pass

def _read (data, offset, length):
  if (len(data)-offset) < length:
    raise UnderrunError("wanted %s bytes but only have %s" % (length, len(data)-offset))
 
    return (offset+length, data[offset:offset+length])

def _unpack (fmt, data, offset):
  size = struct.calcsize(fmt)
  if (len(data)-offset) < size: raise UnderrunError()
  return (offset+size, struct.unpack_from(fmt, data, offset))

def _skip (data, offset, num):
  offset += num
  if offset > len(data): raise UnderrunError()
  return offset

def _unpad (data, offset, num):
  (offset, o) = _read(data, offset, num)
  assert len(o.replace("\x00", "")) == 0
  return offset

def _readzs (data, offset, length):
  #(offset, d) = _read(data, offset, length)

  d = data[offset:offset+length]
  offset += length

  d = d.split("\x00", 1)
  #if len(d[1].replace("\x00", "")) > 0:
  #  raise RuntimeError("Non-zero string padding")
   
  if (len(d) == 1):
    assert True
  else:
    (len(d[1].replace("\x00", "")) == 0)
  return (offset, d[0])

def _readether (data, offset):
  (offset, d) = _read(data, offset, 6)
  return (offset, EthAddr(d))

def _readip (data, offset, networkOrder = True):
  (offset, d) = _read(data, offset, 4)
  return (offset, IPAddr(d, networkOrder = networkOrder))

# ----------------------------------------------------------------------


def _format_body (body, prefix):
  if hasattr(body, 'show'):
    #TODO: Check this (spacing may well be wrong)
    return body.show(prefix + '  ')
  else:
    return prefix + hexdump(body).replace("\n", "\n" + prefix)

TABLE_ALL = 0xff
TABLE_EMERGENCY = 0xfe


class _ofp_meta (type):
  """
  Metaclass for ofp messages/structures

  This takes care of making len() work as desired.
  """
  def __len__ (cls):
    try:
      return cls.__len__()
    except:
      return cls._MIN_LENGTH


class ofp_base (object):
  """
  Base class for OpenFlow messages/structures

  You should implement a __len__ method.  If your length is fixed, it
  should be a static method.  If your length is not fixed, you should
  implement a __len__ instance method and set a class level _MIN_LENGTH
  attribute to your minimum length.
  """
  __metaclass__ = _ofp_meta

  def _assert (self):
    r = self._validate()
    if r is not None:
      raise RuntimeError(r)
      return False # Never reached
    return True

  def _validate (self):
    return None

  def __ne__ (self, other):
    return not self.__eq__(other)

  @classmethod
  def unpack_new (cls, raw, offset=0):
    """
    Unpacks wire format into the appropriate message object.

    Returns newoffset,object
    """
    o = cls()
    r,length = o.unpack(raw, offset)
    
    #log.debug("\nlength " + str(length) + "\noffset " + str(offset) + "\nr " + str(r) + "\nr-offset " + str(r-offset) + '\n')

    #assert (r-offset) == length, o    # TODO enable 
    return (r, o)


# ----------------------------------------------------------------------
# Class decorators
# ----------------------------------------------------------------------

_message_type_to_class = {}
_message_class_to_types = {} # Do we need this?
#_message_type_to_name = {}
#_message_name_to_type = {}
ofp_type_rev_map = {}
ofp_type_map = {}

def openflow_message (ofp_type, type_val, reply_to=None,
    request_for=None, switch=False, controller=False):
  #TODO: Reply stuff, switch/controller stuff

  #_message_name_to_type[ofp_type] = type_val
  #_message_type_to_name[type_val] = ofp_type
  ofp_type_rev_map[ofp_type] = type_val
  ofp_type_map[type_val] = ofp_type
  def f (c):
    c.header_type = type_val
    c._from_switch = switch
    c._from_controller = controller
    _message_type_to_class[type_val] = c
    _message_class_to_types.setdefault(c, set()).add(type_val)
    return c
  return f

# Symmetric Messages
def openflow_sc_message (*args, **kw):
  return openflow_message(switch=True, controller=True, *args, **kw)

# Controller Messages
def openflow_c_message (*args, **kw):
  return openflow_message(controller=True, *args, **kw)

# Switch Messages
def openflow_s_message (*args, **kw):
  return openflow_message(switch=True, *args, **kw)

_queue_prop_type_to_class = {}
_queue_prop_class_to_types = {} # Do we need this?
ofp_queue_prop_type_rev_map = {}
ofp_queue_prop_type_map = {}

def openflow_queue_prop (queue_prop_type, type_val):
  ofp_queue_prop_type_rev_map[queue_prop_type] = type_val
  ofp_queue_prop_type_map[type_val] = queue_prop_type
  def f (c):
    c.property = type_val
    _queue_prop_type_to_class[type_val] = c
    _queue_prop_class_to_types.setdefault(c, set()).add(type_val)
    return c
  return f

# ofp_action preparations
_action_type_to_class = {}
_action_class_to_types = {} # Do we need this?
ofp_action_type_rev_map = {}
ofp_action_type_map = {}

def openflow_action (action_type, type_val):
  ofp_action_type_rev_map[action_type] = type_val
  ofp_action_type_map[type_val] = action_type
  def f (c):
    c.type = type_val
    _action_type_to_class[type_val] = c
    _action_class_to_types.setdefault(c, set()).add(type_val)
    return c
  return f

# ofp_instruction preparations
_instruction_type_to_class = {}
_instruction_class_to_types = {} # Do we need this?
ofp_instruction_type_rev_map = {}
ofp_instruction_type_map = {}

def openflow_instruction (action_type, type_val):
  ofp_instruction_type_rev_map[action_type] = type_val
  ofp_instruction_type_map[type_val] = action_type
  def f (c):
    c.type = type_val
    _action_type_to_class[type_val] = c
    _action_class_to_types.setdefault(c, set()).add(type_val)
    return c
  return f


# multipart messages preparations
class _MultipartClassInfo (object):
  __slots__ = 'request reply reply_is_list'.split()

  def __init__ (self, **kw):
    self.request = None
    self.reply = None
    self.reply_is_list = False
    initHelper(self, kw)

  def __str__ (self):
    r = str(self.reply)
    if self.reply_is_list: r = "[%s]" % (r,)
    return "request:%s reply:%s" % (self.request, r)

_multipart_type_to_class_info = {}
_multipart_class_to_type = {}
ofp_multipart_type_rev_map = {}
ofp_multipart_type_map = {}

# OpenFlow Multipart Request message prototype
def openflow_multipart_request  (multipart_type, type_val=None, is_list=None, is_reply = False):
  if type_val is not None:
    ofp_multipart_type_rev_map[multipart_type] = type_val
    ofp_multipart_type_map[type_val] = multipart_type
  else:
    type_val = ofp_multipart_type_rev_map.get(multipart_type)

  def f (c):
    if type_val is not None:
      ti = _multipart_type_to_class_info.get(multipart_type)
      if ti is not None:
        _multipart_type_to_class_info[type_val] = ti
        del _multipart_type_to_class_info[multipart_type]
      else:
        ti = _multipart_type_to_class_info.setdefault(type_val,
            _MultipartClassInfo())
      _multipart_class_to_type[c] = type_val
    else:
      ti = _multipart_type_to_class_info.setdefault(multipart_type,
          _MultipartClassInfo())

    if is_list is not None:
      ti.reply_is_list = is_list
    if is_reply:
      ti.reply = c
    else:
      ti.request = c

    if type_val is not None:
      yes = False
      if ti.reply is not None and issubclass(ti.reply,ofp_multipart_body_base):
        ti.reply._type = type_val
        yes = True
      if ti.request is not None and issubclass(ti.request,ofp_multipart_body_base):
        ti.request._type = type_val
        yes = True
      assert yes, "Type not set for " + str(multipart_type)

    return c
  return f

# OpenFlow Multipart Reply message prototype
def openflow_multipart_reply (multipart_type, type_val=None, is_list=None, is_reply = True):
  return openflow_multipart_request(multipart_type, type_val, is_list, is_reply)

# ----------------------------------------------------------------------


# ----------------------------------------------------------------------
# Constants, maps, etc.
# ----------------------------------------------------------------------

# Values from macro definitions
OFP_FLOW_PERMANENT = 0
OFP_DL_TYPE_ETH2_CUTOFF = 0x0600
DESC_STR_LEN = 256
OFP_MAX_TABLE_NAME_LEN = 32
#OFPFW_ICMP_CODE = OFPFW_TP_DST
OFPQ_MIN_RATE_UNCFG = 0xffff
OFP_VERSION = 0x04
OFP_MAX_TABLE_NAME_LEN = 32
OFP_DL_TYPE_NOT_ETH_TYPE = 0x05ff
OFP_DEFAULT_MISS_SEND_LEN = 128
OFP_MAX_PORT_NAME_LEN = 16
OFP_SSL_PORT = 6653
#OFPFW_ICMP_TYPE = OFPFW_TP_SRC
OFP_TCP_PORT = 6653
SERIAL_NUM_LEN = 32
OFP_DEFAULT_PRIORITY = 0x8000
OFP_VLAN_NONE = 0xffff
OFPQ_ALL = 0xffffffff
NO_BUFFER = 4294967295
OFPP_MAX = 4294967040

# enum ofp_controller_max_len
ofp_controller_max_len_rev_map = {
  'OFPCML_MAX'         : 0xffe5,   # maximum max_len value which can be used  to request a specific byte length.
  'OFPCML_NO_BUFFER'   : 0xffff,   # indicates that no buffering should be applied and the whole packet is to be sent to the controller.
}


# enum ofp_queue_properties
ofp_queue_properties_rev_map = {
  'OFPQT_MIN_RATE'     : 1,       # Minimum datarate guaranteed.
  'OFPQT_MAX_RATE'     : 2,       # Maximum datarate.
  'OFPQT_EXPERIMENTER' : 0xffff   # Experimenter defined property.
}
OFPQT_NONE         = 0

# enum ofp_capabilities
ofp_capabilities_rev_map = {
  'OFPC_FLOW_STATS'   : 1 << 0,   # Flow statistics.
  'OFPC_TABLE_STATS'  : 1 << 1,   # Table statistics.
  'OFPC_PORT_STATS'   : 1 << 2,   # Port statistics.
  'OFPC_GROUP_STATS'  : 1 << 3,   # Group statistics.
  #'OFPC_RESERVED'     : 1 << 4,
  'OFPC_IP_REASM'     : 1 << 5,   # Can reassemble IP fragments.
  'OFPC_QUEUE_STATS'  : 1 << 6,   # Queue statistics.
  'OFPC_PORT_BLOCKED' : 1 << 8,   # Switch will block looping ports.
}

# enum ofp_config_flags
ofp_config_flags_rev_map = {
  'OFPC_FRAG_NORMAL' : 0,         # No special handling for fragments.
  'OFPC_FRAG_DROP'   : 1,         # Drop fragments.
  'OFPC_FRAG_REASM'  : 2,         # Reassemble (only if OFPC_IP_REASM set).
  'OFPC_FRAG_MASK'   : 3,
}


# enum ofp_multipart_reply_flags
ofp_multipart_reply_flags_rev_map = {
  'OFPMPF_REPLY_MORE' : 1,         # More requests to follow.
}

# enum ofp_packet_in_reason
ofp_packet_in_reason_rev_map = {
  'OFPR_NO_MATCH'      : 0,       # No matching flow.
  'OFPR_ACTION'        : 1,       # Action explicitly output to controller.
  'OFPR_INVALID_TTL'   : 2,       # Packet has invalid TTL.
}
ofp_packet_in_reason_map = {
  0 : 'OFPR_NO_MATCH',
  1 : 'OFPR_ACTION',
  2 : 'OFPR_INVALID_TTL',
}

# enum ofp_flow_removed_reason
ofp_flow_removed_reason_rev_map = {
  'OFPRR_IDLE_TIMEOUT' : 0,       # Flow idle time exceeded idle_timeout.
  'OFPRR_HARD_TIMEOUT' : 1,       # Time exceeded hard_timeout.
  'OFPRR_DELETE'       : 2,       # Evicted by a DELETE flow mod.
  'OFPRR_GROUP_DELETE' : 3        # Group was removed.
}
ofp_flow_removed_reason_map = {
  0 : 'OFPRR_IDLE_TIMEOUT',
  1 : 'OFPRR_HARD_TIMEOUT',
  2 : 'OFPRR_DELETE',
  3 : 'OFPRR_GROUP_DELETE',
}

# enum ofp_hello_elem_type
ofp_hello_elem_type_map = {
  # hello element types
  1 : 'OFPHET_VERSIONBITMAP',    
}

# ----------------------------------------------------------------------
# ports stuff

# enum ofp_port_config
ofp_port_config_rev_map = {
  """
  Flags to indicate behavior of the physical port. These flags are
  used in ofp_port to describe the current configuration. They are
  used in the ofp_port_mod message to configure the port's behavior.
  """
  'OFPPC_PORT_DOWN'    : 1 << 0,  # Port is administratively down.
  'OFPPC_NO_STP'       : 1 << 1,  # Disable 802.1D spanning tree on port.
  'OFPPC_NO_RECV'      : 1 << 2,  # Drop all packets recieved by port.
  'OFPPC_NO_RECV_STP'  : 1 << 3,  # Drop received 802.1D STP packets
  'OFPPC_NO_FLOOD'     : 1 << 4,  # Do not include this port when flooding.
  'OFPPC_NO_FWD'       : 1 << 5,  # Drop packets forwarded to port.
  'OFPPC_NO_PACKET_IN' : 1 << 6,  # Do not send packet-in msgs for port.
}
ofp_port_config_map = {
  1 << 0 : 'OFPPC_PORT_DOWN', 
  1 << 1 : 'OFPPC_NO_STP',
  1 << 2 : 'OFPPC_NO_RECV',
  1 << 3 : 'OFPPC_NO_RECV_STP',
  1 << 4 : 'OFPPC_NO_FLOOD',
  1 << 5 : 'OFPPC_NO_FWD',
  1 << 6 : 'OFPPC_NO_PACKET_IN',
}

# enum ofp_port_state
ofp_port_state_rev_map = {
  """
    Current state of the physical port. 
    These are not configurable from the controller.
  """
  'OFPPS_LINK_DOWN'    : 1 << 1,  # No physical link present.
  'OFPPS_BLOCKED'      : 1 << 2,  # Port is blocked.
  'OFPPS_LIVE'         : 1 << 3,  # Live for Fast Failover Group.
}
ofp_port_state_map = {
  1 << 1 : 'OFPPS_LINK_DOWN',
  1 << 2 : 'OFPPS_BLOCKED',
  1 << 3 : 'OFPPS_LIVE',
}

# enum ofp_port_features
ofp_port_features_rev_map = {
  'OFPPF_10MB_HD' :    1 << 0,    # 10 Mb half-duplex rate support.
  'OFPPF_10MB_FD' :    1 << 1,    # 10 Mb full-duplex rate support.
  'OFPPF_100MB_HD' :   1 << 2,    # 100 Mb half-duplex rate support.
  'OFPPF_100MB_FD' :   1 << 3,    # 100 Mb full-duplex rate support.
  'OFPPF_1GB_HD' :     1 << 4,    # 1 Gb half-duplex rate support.
  'OFPPF_1GB_FD' :     1 << 5,    # 1 Gb full-duplex rate support.
  'OFPPF_10GB_FD' :    1 << 6,    # 10 Gb full-duplex rate support.
  'OFPPF_40GB_FD' :    1 << 7,    # 40 Gb full-duplex rate support.
  'OFPPF_100GB_FD' :   1 << 8,    # 100 Gb full-duplex rate support.
  'OFPPF_1TB_FD' :     1 << 9,    # 1 Tb full-duplex rate support.
  'OFPPF_OTHER' :      1 << 10,   # Other rate, not in the list.
  'OFPPF_COPPER' :     1 << 11,   # Copper medium.
  'OFPPF_FIBER' :      1 << 12,   # Fiber medium.
  'OFPPF_AUTONEG' :    1 << 13,   # Auto-negotiation.
  'OFPPF_PAUSE' :      1 << 14,   # Pause.
  'OFPPF_PAUSE_ASYM' : 1 << 15    # Asymmetric pause.
}
ofp_port_features_map = {
  1 << 0  : 'OFPPF_10MB_HD',
  1 << 1  : 'OFPPF_10MB_FD',
  1 << 2  : 'OFPPF_100MB_HD',
  1 << 3  : 'OFPPF_100MB_FD',
  1 << 4  : 'OFPPF_1GB_HD',
  1 << 5  : 'OFPPF_1GB_FD',
  1 << 6  : 'OFPPF_10GB_FD',
  1 << 7  : 'OFPPF_40GB_FD',
  1 << 8  : 'OFPPF_100GB_FD',
  1 << 9  : 'OFPPF_1TB_FD',
  1 << 10 : 'OFPPF_OTHER',
  1 << 11 : 'OFPPF_COPPER',
  1 << 12 : 'OFPPF_FIBER',
  1 << 13 : 'OFPPF_AUTONEG',
  1 << 14 : 'OFPPF_PAUSE',
  1 << 15 : 'OFPPF_PAUSE_ASYM',
}

# enum ofp_port_reason
ofp_port_reason_rev_map = {
  'OFPPR_ADD'          : 0,       # The port was added.
  'OFPPR_DELETE'       : 1,       # The port was removed.
  'OFPPR_MODIFY'       : 2,       # Some attribute of the port has changed.
}
ofp_port_reason_map = {
  0 : 'OFPPR_ADD',
  1 : 'OFPPR_DELETE',
  2 : 'OFPPR_MODIFY',
}

# enum ofp_port_no
ofp_port_rev_map = {
  """
    Port numbering. Ports are numbered starting from 1.
  """
  # Maximum number of physical and logical switch ports.
  'OFPP_MAX'        : 0xffffff00,

  # Reserved OpenFlow Port ("fake output ports")
  'OFPP_IN_PORT'    : 0xfffffff8,  # Send the packet out the input port. This reserved port must be explicitly used in order to send back out of the input port.
  'OFPP_TABLE'      : 0xfffffff9,  # Submit the packet to the first flow table. NB: This destination port can only be used in packet-out messages.
  'OFPP_NORMAL'     : 0xfffffffa,  # Process with normal L2/L3 switching.
  'OFPP_FLOOD'      : 0xfffffffb,  # All physical ports in VLAN, except input port and those blocked or link down.
  'OFPP_ALL'        : 0xfffffffc,  # All physical ports except input port.
  'OFPP_CONTROLLER' : 0xfffffffd,  # Send to controller.
  'OFPP_LOCAL'      : 0xfffffffe,  # Local openflow "port".
  'OFPP_ANY'        : 0xffffffff,  # Wildcard port used only for flow mod (delete) and flow stats requests. Selects 43 2013; 
                                   # The Open Networking Foundation OpenFlow Switch Specification Version 1.3.2 all flows regardless of output port (including flows with no output port).
}
ofp_port_map = {
  0xffffff00 : 'OFPP_MAX',
  0xfffffff8 : 'OFPP_IN_PORT',
  0xfffffff9 : 'OFPP_TABLE',  
  0xfffffffa : 'OFPP_NORMAL',
  0xfffffffb : 'OFPP_FLOOD', 
  0xfffffffc : 'OFPP_ALL',
  0xfffffffd : 'OFPP_CONTROLLER', 
  0xfffffffe : 'OFPP_LOCAL', 
  0xffffffff : 'OFPP_ANY',  
}


# ----------------------------------------------------------------------
# errors

# enum ofp_error_type
ofp_error_type_rev_map = {
  'OFPET_HELLO_FAILED'          : 0,      # Hello protocol failed.
  'OFPET_BAD_REQUEST'           : 1,      # Request was not understood.
  'OFPET_BAD_ACTION'            : 2,      # Error in action description.
  'OFPET_BAD_INSTRUCTION'       : 3,      # Error in instruction list.
  'OFPET_BAD_MATCH'             : 4,      # Error in match.
  'OFPET_FLOW_MOD_FAILED'       : 5,      # Problem modifying flow entry.
  'OFPET_GROUP_MOD_FAILED'      : 6,      # Problem modifying group entry.
  'OFPET_PORT_MOD_FAILED'       : 7,      # OFPT_PORT_MOD failed.
  'OFPET_TABLE_MOD_FAILED'      : 8,      # Table mod request failed.
  'OFPET_QUEUE_OP_FAILED'       : 9,      # Queue operation failed.
  'OFPET_SWITCH_CONFIG_FAILED'  : 10,     # Switch config request failed.
  'OFPET_ROLE_REQUEST_FAILED'   : 11,     # Controller Role request failed.
  'OFPET_METER_MOD_FAILED'      : 12,     # Error in meter.
  'OFPET_TABLE_FEATURES_FAILED' : 13,     # Setting table features failed.
  'OFPET_EXPERIMENTER'          : 0xffff  # Experimenter error messages.
}

# enum ofp_hello_failed_code
ofp_hello_failed_code_rev_map = {
  'OFPHFC_INCOMPATIBLE' : 0,              # No compatible version.
  'OFPHFC_EPERM'        : 1,              # Permissions error.
}

# enum ofp_bad_request_code
ofp_bad_request_code_rev_map = {
  'OFPBRC_BAD_VERSION'      : 0,          # ofp_header.version not supported.
  'OFPBRC_BAD_TYPE'         : 1,          # ofp_header.type not supported.
  'OFPBRC_BAD_MULTIPART'    : 2,          # ofp_multipart_request.type not supported.
  'OFPBRC_BAD_EXPERIMENTER' : 3,          # Experimenter id not supported (in ofp_experimenter_header or ofp_multipart_request or ofp_multipart_reply).
  'OFPBRC_BAD_EXP_TYPE'     : 4,          # Experimenter type not supported.
  'OFPBRC_EPERM'            : 5,          # Permissions error.
  'OFPBRC_BAD_LEN'          : 6,          # Wrong request length for type.
  'OFPBRC_BUFFER_EMPTY'     : 7,          # Specified buffer has already been used.
  'OFPBRC_BUFFER_UNKNOWN'   : 8,          # Specified buffer does not exist.
  'OFPBRC_BAD_TABLE_ID'     : 9,          # Specified table-id invalid or does not exist.
  'OFPBRC_IS_SLAVE'         : 10,         # Denied because controller is slave.
  'OFPBRC_BAD_PORT'         : 11,         # Invalid port.
  'OFPBRC_BAD_PACKET'       : 12,         # Invalid packet in packet-out
  'OFPBRC_MULTIPART_BUFFER_OVERFLOW' : 13 # ofp_multipart_request overflowed the assigned buffer.
}

# enum ofp_bad_action_code
ofp_bad_action_code_rev_map = {
  'OFPBAC_BAD_TYPE' :           0,        # Unknown action type.
  'OFPBAC_BAD_LEN' :            1,        # Length problem in actions.
  'OFPBAC_BAD_EXPERIMENTER' :   2,        # Unknown experimenter id specified.
  'OFPBAC_BAD_EXP_TYPE' :       3,        # Unknown action type for experimenter id.
  'OFPBAC_BAD_OUT_PORT' :       4,        # Problem validating output action.
  'OFPBAC_BAD_ARGUMENT' :       5,        # Bad action argument.
  'OFPBAC_EPERM' :              6,        # Permissions error.
  'OFPBAC_TOO_MANY' :           7,        # Can't handle this many actions.
  'OFPBAC_BAD_QUEUE' :          8,        # Problem validating output queue.
  'OFPBAC_BAD_OUT_GROUP' :      9,        # Invalid group id in forward action.
  'OFPBAC_MATCH_INCONSISTENT' : 10,       # Action can't apply for this match, or Set-Field missing prerequisite.
  'OFPBAC_UNSUPPORTED_ORDER' :  11,       # Action order is unsupported for the action list in an Apply-Actions instruction
  'OFPBAC_BAD_TAG' :            12,       # Actions uses an unsupported tag/encap.
  'OFPBAC_BAD_SET_TYPE' :       13,       # Unsupported type in SET_FIELD action.
  'OFPBAC_BAD_SET_LEN' :        14,       # Length problem in SET_FIELD action.
  'OFPBAC_BAD_SET_ARGUMENT' :   15        # Bad arguement in SET_FIELD action.
}

# enum ofp_flow_mod_failed_code
ofp_flow_mod_failed_code_rev_map = {
  'OFPFMFC_UNKNOWN' :      0,             # Unspecified error.
  'OFPFMFC_TABLES_FULL' :  1,             # Flow not added because table was full.
  'OFPFMFC_BAD_TABLE_ID' : 2,             # Table does not exist
  'OFPFMFC_OVERLAP' :      3,             # Attempted to add overlapping flow with CHECK_OVERLAP flag set.
  'OFPFMFC_EPERM' :        4,             # Permissions error.
  'OFPFMFC_BAD_TIMEOUT' :  5,             # Flow not added because of unsupported idle/hard timeout.
  'OFPFMFC_BAD_COMMAND' :  6,             # Unsupported or unknown command.
  'OFPFMFC_BAD_FLAGS' :    7              # Unsupported or unknown flags.
}

# enum ofp_port_mod_failed_code
ofp_port_mod_failed_code_rev_map = {
  'OFPPMFC_BAD_PORT' :      0,            # Specified port does not exist.
  'OFPPMFC_BAD_HW_ADDR' :   1,            # Specified hardware address does not match the port number.
  'OFPPMFC_BAD_CONFIG' :    2,            # Specified config is invalid.
  'OFPPMFC_BAD_ADVERTISE' : 3,            # Specified advertise is invalid.
  'OFPPMFC_EPERM' :         4             # Permissions error.
}

# enum ofp_queue_op_failed_code
ofp_queue_op_failed_code_rev_map = {
  'OFPQOFC_BAD_PORT'  : 0,                # Invalid port (or port does not exist).
  'OFPQOFC_BAD_QUEUE' : 1,                # Queue does not exist.
  'OFPQOFC_EPERM'     : 2,                # Permissions error.
}


# ----------------------------------------------------------------------
# groups

# enum ofp_group
OFPG_MAX = 0xffffff00  # Last usable group number.
#Fake groups
OFPG_ALL = 0xfffffffc  # Represents all groups for group delete commands.
OFPG_ANY = 0xffffffff  # Wildcard group used only for flow stats requests.
                       # Selects all flows regardless of group (including flows with no group).
ofp_group_map = {
  0xffffff00 : 'OFPG_MAX',
  0xfffffffc : 'OFPG_ALL',
  0xffffffff : 'OFPG_ANY',   
}


# enum ofp_group_capabilities
ofp_group_capabilities_map = {
  # Group configuration flags
  1 << 0 : 'OFPGFC_SELECT_WEIGHT',      # Support weight for select groups 
  1 << 1 : 'OFPGFC_SELECT_LIVENESS',    # Support liveness for select groups 
  1 << 2 : 'OFPGFC_CHAINING',           # Support chaining groups 
  1 << 3 : 'OFPGFC_CHAINING_CHECKS',    # Check chaining for loops and delete 
}


# enum ofp_group_type
ofp_group_type_map = {
  # Group types. Values in the range [128, 255] are reserved for experimental use. 
  0 : 'OFPGT_ALL',              # All (multicast/broadcast) group. 
  1 : 'OFPGT_SELECT',           # Select group. 
  2 : 'OFPGT_INDIRECT',         # Indirect group. 
  3 : 'OFPGT_FF',               # Fast failover group. 
}

# enum ofp_group_mod_command
ofp_group_mod_command_map = {
  # Group commands. 
  0 : 'OFPGC_ADD',              # New group.
  1 : 'OFPGC_MODIFY',           # Modify all matching groups.
  2 : 'OFPGC_DELETE',           # Delete all matching groups. 
}

# ----------------------------------------------------------------------
# actions

# enum ofp_action_type
ofp_action_type_map = {
  0 : "OFPAT_OUTPUT",           # Output to switch port. 
  11 : "OFPAT_COPY_TTL_OUT",    # Copy TTL "outwards" -- from next-to-outermost to outermost 
  12 : "OFPAT_COPY_TTL_IN",     # Copy TTL "inwards" -- from outermost to next-to-outermost 
  15 : "OFPAT_SET_MPLS_TTL",    # MPLS TTL 
  16 : "OFPAT_DEC_MPLS_TTL",    # Decrement MPLS TTL 
  17 : "OFPAT_PUSH_VLAN",       # Push a new VLAN tag 
  18 : "OFPAT_POP_VLAN",        # Pop the outer VLAN tag 
  19 : "OFPAT_PUSH_MPLS",       # Push a new MPLS tag 
  20 : "OFPAT_POP_MPLS",        # Pop the outer MPLS tag 
  21 : "OFPAT_SET_QUEUE",       # Set queue id when outputting to a port 
  22 : "OFPAT_GROUP",           # Apply group. 
  23 : "OFPAT_SET_NW_TTL",      # IP TTL. 
  24 : "OFPAT_DEC_NW_TTL",      # Decrement IP TTL. 
  25 : "OFPAT_SET_FIELD",       # Set a header field using OXM TLV format. 
  26 : "OFPAT_PUSH_PBB",        # Push a new PBB service tag (I-TAG) 
  27 : "OFPAT_POP_PBB",         # Pop the outer PBB service tag (I-TAG) 
  0xffff : "OFPAT_EXPERIMENTER", 
};

# ----------------------------------------------------------------------
# meters

# enum ofp_meter
ofp_meter_map = {
  # Meter numbering. Flow meters can use any number up to OFPM_MAX.
  0xffff0000 : 'OFPM_MAX',          # Last usable meter.
  # Virtual meters. 
  0xfffffffd : 'OFPM_SLOWPATH',     # Meter for slow datapath. 
  0xfffffffe : 'OFPM_CONTROLLER',   # Meter for controller connection. 
  0xffffffff : 'OFPM_ALL',          # Represents all meters for stat requests commands. 
}
ofp_meter_rev_map = {
  'OFPM_MAX' : 0xffff0000,
  'OFPM_SLOWPATH' : 0xfffffffd,
  'OFPM_CONTROLLER' : 0xfffffffe,
  'OFPM_ALL' : 0xffffffff,
}

# enum ofp_meter_mod_command
# TODO - don't know if the numbers are correct since there are none in the specification
ofp_meter_mod_command_map = {
  # Meter commands 
  0 : 'OFPMC_ADD',                  # New meter.
  1 : 'OFPMC_MODIFY',               # Modify specified meter.
  2 : 'OFPMC_DELETE',               # Delete specified meter.
}


# enum ofp_meter_flags
ofp_meter_flags_map = {
  # Meter configuration flags 
  1 << 0 : 'OFPMF_KBPS',            # Rate value in kb/s (kilo-bit per second).
  1 << 1 : 'OFPMF_PKTPS',           # Rate value in packet/sec.
  1 << 2 : 'OFPMF_BURST',           # Do burst size.
  1 << 3 : 'OFPMF_STATS',           # Collect statistics.
}

# enum ofp_meter_band_type
ofp_meter_band_type_map = {
  # Meter band types 
  1 : 'OFPMBT_DROP',                # Drop packet.
  2 : 'OFPMBT_DSCP_REMARK',         # Remark DSCP in the IP header.
  0xFFFF : 'OFPMBT_EXPERIMENTER',   # Experimenter meter band.
}
ofp_meter_band_type_rev_map = {
  'OFPMBT_DROP' : 1,
  'OFPMBT_DSCP_REMARK' : 2,
  'OFPMBT_EXPERIMENTER' : 0xFFFF,
}


# ----------------------------------------------------------------------
# table features

# enum ofp_table 
ofp_table_rev_map = { 
  # table numbering
  'OFPTT_MAX' : 0xfe,               # Last usable table number.
  'OFPTT_ALL' : 0xff,               # Wildcard table used for table config, flow stats and flow deletes.
}
ofp_table_map = {
  0xfe : 'OFPTT_MAX',
  0xff : 'OFPTT_ALL',  
}

# enum ofp_table_feature_prop_type
ofp_table_feature_prop_type_rev_map = {
  """
  Table Feature property types.
  Low order bit cleared indicates a property for a regular Flow Entry.
  Low order bit set indicates a property for the Table-Miss Flow Entry.
  """
  'OFPTFPT_INSTRUCTIONS' : 0,           # Instructions property.
  'OFPTFPT_INSTRUCTIONS_MISS' : 1,      # Instructions for table-miss.
  'OFPTFPT_NEXT_TABLES' : 2,            # Next Table property.
  'OFPTFPT_NEXT_TABLES_MISS' : 3,       # Next Table for table-miss.
  'OFPTFPT_WRITE_ACTIONS' : 4,          # Write Actions property.
  'OFPTFPT_WRITE_ACTIONS_MISS' : 5,     # Write Actions for table-miss.
  'OFPTFPT_APPLY_ACTIONS' : 6,          # Apply Actions property.
  'OFPTFPT_APPLY_ACTIONS_MISS' : 7,     # Apply Actions for table-miss.
  'OFPTFPT_MATCH' : 8,                  # Match property.
  'OFPTFPT_WILDCARDS' : 10,             # Wildcards property.
  'OFPTFPT_WRITE_SETFIELD' : 12,        # Write Set-Field property.
  'OFPTFPT_WRITE_SETFIELD_MISS' : 13,   # Write Set-Field for table-miss.
  'OFPTFPT_APPLY_SETFIELD' : 14,        # Apply Set-Field property.
  'OFPTFPT_APPLY_SETFIELD_MISS' : 15,   # Apply Set-Field for table-miss.
  'OFPTFPT_EXPERIMENTER' : 0xFFFE,      # Experimenter property.
  'OFPTFPT_EXPERIMENTER_MISS' : 0xFFFF, # Experimenter for table-miss.
}
ofp_table_feature_prop_type_map = {
  0 : 'OFPTFPT_INSTRUCTIONS',
  1 : 'OFPTFPT_INSTRUCTIONS_MISS',
  2 : 'OFPTFPT_NEXT_TABLES',
  3 : 'OFPTFPT_NEXT_TABLES_MISS',
  4 : 'OFPTFPT_WRITE_ACTIONS',
  5 : 'OFPTFPT_WRITE_ACTIONS_MISS',
  6 : 'OFPTFPT_APPLY_ACTIONS',
  7 : 'OFPTFPT_APPLY_ACTIONS_MISS',
  8 : 'OFPTFPT_MATCH',
  10 : 'OFPTFPT_WILDCARDS',
  12 : 'OFPTFPT_WRITE_SETFIELD',
  13 : 'OFPTFPT_WRITE_SETFIELD_MISS',
  14 : 'OFPTFPT_APPLY_SETFIELD',
  15 : 'OFPTFPT_APPLY_SETFIELD_MISS',
  0xFFFE : 'OFPTFPT_EXPERIMENTER',
  0xFFFF : 'OFPTFPT_EXPERIMENTER_MISS',
}

# ----------------------------------------------------------------------
# flow matching

# flow wildcards
# TODO update
OFPFW_NW_DST_BITS      = 6
OFPFW_NW_SRC_BITS      = 6
OFPFW_NW_SRC_SHIFT     = 8
OFPFW_NW_DST_SHIFT     = 14
OFPFW_NW_SRC_ALL       = 8192
OFPFW_NW_SRC_MASK      = 16128
OFPFW_NW_DST_ALL       = 524288
OFPFW_NW_DST_MASK      = 1032192
# Note: Need to handle all flags that are set in this.
# glob-all masks in the packet handling methods.
# (Esp. ofp_match.from_packet)
# Otherwise, packets are not being matched as they should
OFPFW_ALL              = ((1 << 22) - 1)

# enum ofp_flow_mod_command
ofp_flow_mod_command_rev_map = {
  'OFPFC_ADD'           : 0,      # New flow.
  'OFPFC_MODIFY'        : 1,      # Modify all matching flows.
  'OFPFC_MODIFY_STRICT' : 2,      # Modify entry strictly matching wildcards
  'OFPFC_DELETE'        : 3,      # Delete all matching flows.
  'OFPFC_DELETE_STRICT' : 4,      # Strictly match wildcards and priority.
}

# enum ofp_flow_mod_flags
ofp_flow_mod_flags_rev_map = {
  'OFPFF_SEND_FLOW_REM' : 1,      # Send flow removed message when flow expires or is deleted.
  'OFPFF_CHECK_OVERLAP' : 2,      # Check for overlapping entries first.
  #'OFPFF_EMERG'         : 4,
  'OFPFF_RESET_COUNT' :   4,      # Reset flow packet and byte counts.
  'OFPFF_NO_PKT_COUNTS' : 8,      # Don't keep track of packet count.
  'OFPFF_NO_BYT_COUNTS' : 16      # Don't keep track of byte count.
}

# enum ofp_flow_wildcards
ofp_flow_wildcards_rev_map = {
  'OFPFW_IN_PORT'      : 1 << 0,   # Switch input port.
  'OFPFW_DL_VLAN'      : 1 << 1,   # VLAN.
  'OFPFW_DL_SRC'       : 1 << 2,   # Ethernet source address.
  'OFPFW_DL_DST'       : 1 << 3,   # Ethernet destination address.
  'OFPFW_DL_TYPE'      : 1 << 4,   # Ethernet frame type.
  'OFPFW_NW_PROTO'     : 1 << 5,   # 
  'OFPFW_TP_SRC'       : 1 << 6,   # 
  'OFPFW_TP_DST'       : 1 << 7,   # 

  """
    IP source address wildcard bit count. 0 is exact match, 1 ignores the
    LSB, 2 ignores the 2 least-significant bits, ..., 32 and higher wildcard
    the entire field. This is the *opposite* of the usual convention where
    e.g. /24 indicates that 8 bits (not 24 bits) are wildcarded. 
  """
  'OFPFW_NW_SRC_SHIFT'  : 8,
  'OFPFW_NW_SRC_BITS'   : 6,
  'OFPFW_NW_SRC_MASK'   : ((1 << OFPFW_NW_SRC_BITS) - 1) << OFPFW_NW_SRC_SHIFT,
  'OFPFW_NW_SRC_ALL'    : 32 << OFPFW_NW_SRC_SHIFT,

   # IP destination address wildcard bit count. Same format as source.
  'OFPFW_NW_DST_SHIFT'  : 14,
  'OFPFW_NW_DST_BITS'   : 6,
  'OFPFW_NW_DST_MASK'   : ((1 << OFPFW_NW_DST_BITS) - 1) << OFPFW_NW_DST_SHIFT,
  'OFPFW_NW_DST_ALL'    : 32 << OFPFW_NW_DST_SHIFT,

  #'OFPFW_DL_VLAN_PCP'  : 1<<20,     
  #'OFPFW_NW_TOS'       : 1<<21,    
}

# enum ofp_match_type
ofp_match_type_rev_map = {
  'OFPMT_STANDARD'  : 0,                  # Deprecated
  'OFPMT_OXM'       : 1,                  # OpenFlow Extensible Match
}


# enum ofp_oxm_class
OFPXMC_NXM_0 = 0x0000  # Backward compatibility with NXM
OFPXMC_NXM_1 = 0x0001  # Backward compatibility with NXM
OFPXMC_OPENFLOW_BASIC = 0x8000  # Basic class for OpenFlow
OFPXMC_EXPERIMENTER = 0xFFFF  # Experimenter class

# OXM maps
ofp_oxm_class_map = {
    0x0000 : 'OFPXMC_NXM_0',
    0x0001 : 'OFPXMC_NXM_1',
    0x8000 : 'OFPXMC_OPENFLOW_BASIC',
    0xFFFF : 'OFPXMC_EXPERIMENTER',
}
ofp_oxm_class_rev_map = {
    'OFPXMC_NXM_0' : 0x0000,
    'OFPXMC_NXM_1' : 0x0001,
    'OFPXMC_OPENFLOW_BASIC' : 0x8000,
    'OFPXMC_EXPERIMENTER' : 0xFFFF,
}

# OXM types for oxm_class OFPXMC_OPENFLOW_BASIC
oxm_ofb_match_fields_rev_map = {
    # values from enum oxm_ofb_match_fields
    'OFPXMT_OFB_IN_PORT' : 0,         # Switch input port. 
    'OFPXMT_OFB_IN_PHY_PORT' : 1,     # Switch physical input port. 
    'OFPXMT_OFB_METADATA' : 2,        # Metadata passed between tables. 
    'OFPXMT_OFB_ETH_DST' : 3,         # Ethernet destination address. 
    'OFPXMT_OFB_ETH_SRC' : 4,         # Ethernet source address. 
    'OFPXMT_OFB_ETH_TYPE' : 5,        # Ethernet frame type. 
    'OFPXMT_OFB_VLAN_VID' : 6,        # VLAN id. 
    'OFPXMT_OFB_VLAN_PCP' : 7,        # VLAN priority. 
    'OFPXMT_OFB_IP_DSCP' : 8,         # IP DSCP (6 bits in ToS field). 
    'OFPXMT_OFB_IP_ECN' : 9,          # IP ECN (2 bits in ToS field). 
    'OFPXMT_OFB_IP_PROTO' : 10,       # IP protocol. 
    'OFPXMT_OFB_IPV4_SRC' : 11,       # IPv4 source address. 
    'OFPXMT_OFB_IPV4_DST' : 12,       # IPv4 destination address. 
    'OFPXMT_OFB_TCP_SRC' : 13,        # TCP source port. 
    'OFPXMT_OFB_TCP_DST' : 14,        # TCP destination port. 
    'OFPXMT_OFB_UDP_SRC' : 15,        # UDP source port. 
    'OFPXMT_OFB_UDP_DST' : 16,        # UDP destination port. 
    'OFPXMT_OFB_SCTP_SRC' : 17,       # SCTP source port. 
    'OFPXMT_OFB_SCTP_DST' : 18,       # SCTP destination port. 
    'OFPXMT_OFB_ICMPV4_TYPE' : 19,    # ICMP type. 
    'OFPXMT_OFB_ICMPV4_CODE' : 20,    # ICMP code. 
    'OFPXMT_OFB_ARP_OP' : 21,         # ARP opcode. 
    'OFPXMT_OFB_ARP_SPA' : 22,        # ARP source IPv4 address. 
    'OFPXMT_OFB_ARP_TPA' : 23,        # ARP target IPv4 address. 
    'OFPXMT_OFB_ARP_SHA' : 24,        # ARP source hardware address. 
    'OFPXMT_OFB_ARP_THA' : 25,        # ARP target hardware address.
    'OFPXMT_OFB_IPV6_SRC' : 26,       # IPv6 source address. 
    'OFPXMT_OFB_IPV6_DST' : 27,       # IPv6 destination address. 
    'OFPXMT_OFB_IPV6_FLABEL' : 28,    # IPv6 Flow Label 
    'OFPXMT_OFB_ICMPV6_TYPE' : 29,    # ICMPv6 type. 
    'OFPXMT_OFB_ICMPV6_CODE' : 30,    # ICMPv6 code. 
    'OFPXMT_OFB_IPV6_ND_TARGET' : 31, # Target address for ND. 
    'OFPXMT_OFB_IPV6_ND_SLL' : 32,    # Source link-layer for ND. 
    'OFPXMT_OFB_IPV6_ND_TLL' : 33,    # Target link-layer for ND. 
    'OFPXMT_OFB_MPLS_LABEL' : 34,     # MPLS label. 
    'OFPXMT_OFB_MPLS_TC' : 35,        # MPLS TC. 
    'OFPXMT_OFB_MPLS_BOS' : 36,       # MPLS BoS bit. 
    'OFPXMT_OFB_PBB_ISID' : 37,       # PBB I-SID. 
    'OFPXMT_OFB_TUNNEL_ID' : 38,      # Logical Port Metadata. 
    'OFPXMT_OFB_IPV6_EXTHDR' : 39,    # IPv6 Extension Header pseudo-field 

    """
     values from OF 1.3.2 table 12 that represent the same OXMs as above
       with different prefix
    """
    'OXM_OF_IN_PORT' : 0,
    'OXM_OF_IN_PHY_PORT' : 1,
    'OXM_OF_METADATA' : 2,
    'OXM_OF_ETH_DST' : 3,
    'OXM_OF_ETH_SRC' : 4,
    'OXM_OF_ETH_TYPE' : 5,
    'OXM_OF_VLAN_VID' : 6,
    'OXM_OF_VLAN_PCP' : 7,
    'OXM_OF_IP_DSCP' : 8,
    'OXM_OF_IP_ECN' : 9,
    'OXM_OF_IP_PROTO' : 10,
    'OXM_OF_IPV4_SRC' : 11,
    'OXM_OF_IPV4_DST' : 12,
    'OXM_OF_TCP_SRC' : 13,
    'OXM_OF_TCP_DST' : 14,
    'OXM_OF_UDP_SRC' : 15,
    'OXM_OF_UDP_DST' : 16,
    'OXM_OF_SCTP_SRC' : 17,
    'OXM_OF_SCTP_DST' : 18,
    'OXM_OF_ICMPV4_TYPE' : 19, 
    'OXM_OF_ICMPV4_CODE' : 20,
    'OXM_OF_ARP_OP' : 21,
    'OXM_OF_ARP_SPA' : 22,
    'OXM_OF_ARP_TPA' : 23,
    'OXM_OF_ARP_SHA' : 24,
    'OXM_OF_ARP_THA' : 25,
    'OXM_OF_IPV6_SRC' : 26,
    'OXM_OF_IPV6_DST' : 27,
    'OXM_OF_IPV6_FLABEL' : 28,
    'OXM_OF_ICMPV6_TYPE' : 29,
    'OXM_OF_ICMPV6_CODE' : 30,
    'OXM_OF_IPV6_ND_TARGET' : 31,
    'OXM_OF_IPV6_ND_SLL' : 32,
    'OXM_OF_IPV6_ND_TLL' : 33,
    'OXM_OF_MPLS_LABEL' : 34,
    'OXM_OF_MPLS_TC' : 35,
    'OXM_OF_MPLS_BOS' : 36,
    'OXM_OF_PBB_ISID' : 37,
    'OXM_OF_TUNNEL_ID' : 38,
    'OXM_OF_IPV6_EXTHDR' : 39,
}

oxm_ofb_match_fields_map = {
    0 : 'OFPXMT_OFB_IN_PORT',         # Switch input port. 
    1 : 'OFPXMT_OFB_IN_PHY_PORT',     # Switch physical input port. 
    2 : 'OFPXMT_OFB_METADATA',        # Metadata passed between tables. 
    3 : 'OFPXMT_OFB_ETH_DST',         # Ethernet destination address. 
    4 : 'OFPXMT_OFB_ETH_SRC',         # Ethernet source address. 
    5 : 'OFPXMT_OFB_ETH_TYPE',        # Ethernet frame type. 
    6 : 'OFPXMT_OFB_VLAN_VID',        # VLAN id. 
    7 : 'OFPXMT_OFB_VLAN_PCP',        # VLAN priority. 
    8 : 'OFPXMT_OFB_IP_DSCP',         # IP DSCP (6 bits in ToS field). 
    9 : 'OFPXMT_OFB_IP_ECN',          # IP ECN (2 bits in ToS field). 
    10 : 'OFPXMT_OFB_IP_PROTO',       # IP protocol. 
    11 : 'OFPXMT_OFB_IPV4_SRC',       # IPv4 source address. 
    12 : 'OFPXMT_OFB_IPV4_DST',       # IPv4 destination address. 
    13 : 'OFPXMT_OFB_TCP_SRC',        # TCP source port. 
    14 : 'OFPXMT_OFB_TCP_DST',        # TCP destination port. 
    15 : 'OFPXMT_OFB_UDP_SRC',        # UDP source port. 
    16 : 'OFPXMT_OFB_UDP_DST',        # UDP destination port. 
    17 : 'OFPXMT_OFB_SCTP_SRC',       # SCTP source port. 
    18 : 'OFPXMT_OFB_SCTP_DST',       # SCTP destination port. 
    19 : 'OFPXMT_OFB_ICMPV4_TYPE',    # ICMP type. 
    20 : 'OFPXMT_OFB_ICMPV4_CODE',    # ICMP code. 
    21 : 'OFPXMT_OFB_ARP_OP',         # ARP opcode. 
    22 : 'OFPXMT_OFB_ARP_SPA',        # ARP source IPv4 address. 
    23 : 'OFPXMT_OFB_ARP_TPA',        # ARP target IPv4 address. 
    24 : 'OFPXMT_OFB_ARP_SHA',        # ARP source hardware address. 
    25 : 'OFPXMT_OFB_ARP_THA',        # ARP target hardware address.
    26 : 'OFPXMT_OFB_IPV6_SRC',       # IPv6 source address. 
    27 : 'OFPXMT_OFB_IPV6_DST',       # IPv6 destination address. 
    28 : 'OFPXMT_OFB_IPV6_FLABEL',    # IPv6 Flow Label 
    29 : 'OFPXMT_OFB_ICMPV6_TYPE',    # ICMPv6 type. 
    30 : 'OFPXMT_OFB_ICMPV6_CODE',    # ICMPv6 code. 
    31 : 'OFPXMT_OFB_IPV6_ND_TARGET', # Target address for ND. 
    32 : 'OFPXMT_OFB_IPV6_ND_SLL',    # Source link-layer for ND. 
    33 : 'OFPXMT_OFB_IPV6_ND_TLL',    # Target link-layer for ND. 
    34 : 'OFPXMT_OFB_MPLS_LABEL',     # MPLS label. 
    35 : 'OFPXMT_OFB_MPLS_TC',        # MPLS TC. 
    36 : 'OFPXMT_OFB_MPLS_BOS',       # MPLS BoS bit. 
    37 : 'OFPXMT_OFB_PBB_ISID',       # PBB I-SID. 
    38 : 'OFPXMT_OFB_TUNNEL_ID',      # Logical Port Metadata. 
    39 : 'OFPXMT_OFB_IPV6_EXTHDR',    # IPv6 Extension Header pseudo-field 
}

# ofp_match structure
ofp_match_data = {
  # match structure fields 
  'in_port'     : 0,            # OFPXMT_OFB_IN_PORT
  'dl_src'      : EMPTY_ETH,    # OFPXMT_OFB_ETH_SRC
  'dl_dst'      : EMPTY_ETH,    # OFPXMT_OFB_ETH_DST
  'dl_vlan'     : 0,            # OFPXMT_OFB_VLAN_VID
  'dl_vlan_pcp' : 0,            # OFPXMT_OFB_VLAN_PCP
  'dl_type'     : 0,            # OFPXMT_OFB_ETH_TYPE
  'nw_tos'      : 0,            # OFPXMT_OFB_IP_DSCP (ToS bits 0-5)
                                #   + OFPXMT_OFB_IP_ECN (ToS bits 6-7)
  'nw_proto'    : 0,            # OFPXMT_OFB_IP_PROTO
  'nw_src'      : 0,            # OFPXMT_OFB_IPV4_SRC / OFPXMT_OFB_IPV6_SRC
  'nw_dst'      : 0,            # OFPXMT_OFB_IPV4_DST / OFPXMT_OFB_IPV6_DST
  'tp_src'      : 0,            # OFPXMT_OFB_UDP_SRC / OFPXMT_OFB_TCP_SRC
  'tp_dst'      : 0,            # OFPXMT_OFB_UDP_DST / OFPXMT_OFB_TCP_DST

  # new fields
  'type'        :  ofp_match_type_rev_map['OFPMT_OXM'],
  'length'      :  4,
  'oxm_fields_pkt':  [],
}

# ----------------------------------------------------------------------
# roles

# enum ofp_controller_role
ofp_controller_role_map = {
  # Controller roles.
  0 : 'OFPCR_ROLE_NOCHANGE',
  1 : 'OFPCR_ROLE_EQUAL', 
  2 : 'OFPCR_ROLE_MASTER', 
  3 : 'OFPCR_ROLE_SLAVE', 
}

# ----------------------------------------------------------------------
# Structure definitions
# ----------------------------------------------------------------------
## Openflow Header
# ----------------------------------------------------------------------
class ofp_header (ofp_base):
  _MIN_LENGTH = 8
  def __init__ (self, **kw):
    self.version = OFP_VERSION
    #self.header_type = None # Set via class decorator
    self._xid = None
    if 'header_type' in kw:
      self.header_type = kw.pop('header_type')
    initHelper(self, kw)

  @property
  def xid (self):
    if self._xid is None:
      self._xid = generate_xid()
    return self._xid

  @xid.setter
  def xid (self, val):
    self._xid = val

  def _validate (self):
    if self.header_type not in ofp_type_map:
      return "type is not a known message type"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!BBHI", 
                          self.version, 
                          self.header_type, 
                          len(self), 
                          self.xid)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    log.debug("Header len %d", length)
    return offset,length

  def _unpack_header (self, raw, offset):
    offset,(self.version, self.header_type, length, self.xid) = \
        _unpack("!BBHI", raw, offset)
    return offset,length

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.version != other.version: return False
    if self.header_type != other.header_type: return False
    if len(self) != len(other): return False
    if self.xid != other.xid: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'version: ' + str(self.version) + '\n'
    outstr += prefix + 'type:    ' + str(self.header_type)# + '\n'
    outstr += " (" + ofp_type_map.get(self.header_type, "Unknown") + ")\n"
    try:
      outstr += prefix + 'length:  ' + str(len(self)) + '\n'
    except:
      pass
    outstr += prefix + 'xid:     ' + str(self.xid) + '\n'
    return outstr

  def __str__ (self):
    return self.__class__.__name__ + "\n  " + self.show('  ').strip()

# ----------------------------------------------------------------------
# hello element header
# ----------------------------------------------------------------------
class ofp_hello_elem_header:
  def __init__ (self, **kw):
    self.type = 0
    self.length = 4
    self.value = b''

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HH", 
                          self.type,
                          self.length)
    packed += self.value[0:self.length  -4]

    # padding specified for OFPHET_VERSIONBITMAP is not specified
    #  for generic header
    if self.type == 1:
      length_pad = (8 - (self.length % 8)) % 8
      pad_string = "!" + str(length_pad) + "x"
      packed += struct.pack(pad_string)

    return packed

  def unpack(self, raw, offset):
    offset, (self.type,
             self.length) = _unpack("!HH", raw, offset)
    self.value = raw[offset:offset-4+self.length]
    offset += self.length-4 

    # padding specified for OFPHET_VERSIONBITMAP is not specified
    #  for generic header
    if self.type == 1:
      length_pad = (8 - (self.length % 8)) % 8
      offset += length_pad

    return offset

  def __len__(self):
    return self.length 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'type: '   + ofp_hello_elem_type_map.get(self.type, str(self.type)) + '\n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'value: '  + binascii.hexlify(self.value) + '\n'
    return outstr

  

# ----------------------------------------------------------------------
# Base class for queue properties
# ----------------------------------------------------------------------
class ofp_queue_prop_base (ofp_base):
  """
  This is sort of the equivalent of ofp_queue_prop_header in the spec.
  However, ofp_queue_prop_header as the spec defines it is not super
  useful for us, as it has the padding in it.
  """
  property = None

# ----------------------------------------------------------------------
## Group Structures
# ----------------------------------------------------------------------

# bucket counter
class ofp_bucket_counter:
  def __init__ (self, **kw):
    self.packet_count = 0
    self.byte_count = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("QQ", 
                          self.packet_count,
                          self.byte_count)
    return packed

  def unpack(self, raw, offset):
    offset,(self.packet_count,
            self.byte_count) = _unpack("!QQ", raw, offset)
    return offset

  def __len__(self):
    return 16 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'packet count: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'byte count: ' + str(self.byte_count) + '\n'
    return outstr

# ofp_bucket
class ofp_bucket:
  def __init__ (self, **kw):
    self.len = 0    # Length the bucket in bytes, including this header and  
                    #  any padding to make it 64-bit aligned.
    self.weight = 0
    self.watch_port = 0
    self.watch_group = 0
    self.actions = []

    initHelper(self, kw)

  # packing of whole message
  def pack (self):
    packed  = b''
    packed += struct.pack("HHLL4x", 
                          self.len,
                          self.byte_count,
                          self.watch_port,
                          self.watch_group,)

    # pack actions
    actionspkd = b""
    for action in self.actions:
      if action:
        packed += action.pack()

    return packed

  # unpacking of actions from ofp_instruction_actions
  def _unpack_actions (b, length, offset=0):
    """
    Parses actions from a buffer  b is a buffer (bytes)
    offset, if specified, is where in b to start decoding
    returns (next_offset, [Actions])
    """
    if (len(b) - offset) < length: raise UnderrunError
    actions = []
    end = length + offset
    while offset < end:
      (t,l) = struct.unpack_from("!HH", b, offset)
      if (len(b) - offset) < l: raise UnderrunError
      a = _action_type_to_class.get(t)
      if a is None:
        # Use generic action header for unknown type
        a = ofp_action_generic()
      else:
        a = a()
      a.unpack(b[offset:offset+l])
      assert len(a) == l
      actions.append(a)
      offset += l
    return (offset, actions)

  # unpacking of whole message
  def unpack(self, raw, offset):
    offset,(self.len,
            self.byte_count,
            self.watch_port,
            self.watch_group) = _unpack("!HHLL4x", raw, offset)

    offset, self.actions = _unpack_actions(raw, self.len - 16,  offset)

    return offset

  def __len__(self):
    return 16 + sum(len(action) for action in self.actions)

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'length: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'weight: ' + str(self.byte_count) + '\n'
    outstr += prefix + 'watch port: ' + str(self.watch_port) + '\n'
    outstr += prefix + 'watch group: ' + str(self.watch_group) + '\n'

    outstr += prefix + 'actions: \n'
    if self.actions:
      for action in self.actions:
        if action is not None:
          outstr += action.show(prefix + '  ')
   
    return outstr

# ----------------------------------------------------------------------
## Meter Structures
# ----------------------------------------------------------------------
# meter band stats class
class ofp_meter_band_stats:
  def __init__ (self, **kw):
    self.packet_band_count = 0
    self.byte_band_count = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("QQ", 
                          self.packet_band_count,
                          self.byte_band_count)
    return packed

  def unpack(self, raw, offset):
    offset,(self.packet_band_count,
            self.byte_band_count) = _unpack("!QQ", raw, offset)
    return offset

  def __len__(self):
    return 16 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'packet count: ' + str(self.packet_band_count) + '\n'
    outstr += prefix + 'byte count: ' + str(self.byte_band_count) + '\n'
    return outstr

# Common header for all meter bands
class ofp_meter_band_header:
  def __init__ (self, **kw):
    self.type = 0
    self.length = 0
    self.rate = 0
    self.burst_size = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HHLL", 
                          self.type,
                          self.length,
                          self.rate,
                          self.burst_size)
    return packed

  def unpack(self, raw, offset):
    offset,(self.type,
            self.length,
            self.rate,
            self.burst_size) = _unpack("!HHLL", raw, offset)
    return offset

  def __len__(self):
    return 12 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'type: ' + ofp_meter_band_type_map.get(self.type,str(self.type)) + '\n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'rate: ' + str(self.rate) + '\n'
    outstr += prefix + 'burst_size: ' + str(self.burst_size) + '\n'
    return outstr

# drop packets
class ofp_meter_band_drop:
  def __init__ (self, **kw):
    self.type = ofp_meter_band_type_rev_map['OFPMBT_DROP']
    self.length = 0
    self.rate = 0
    self.burst_size = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HHLL4x", 
                          ofp_meter_band_type_rev_map['OFPMBT_DROP'],
                          self.length,
                          self.rate,
                          self.burst_size)
    return packed

  def unpack(self, raw, offset):
    offset,(self.type,
            self.length,
            self.rate,
            self.burst_size) = _unpack("!HHLL4x", raw, offset)
    return offset

  def __len__(self):
    return 16 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'type: OFPMBT_DROP \n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'rate: ' + str(self.rate) + '\n'
    outstr += prefix + 'burst_size: ' + str(self.burst_size) + '\n'
    return outstr

# remark DSCP in the IP header
class ofp_meter_band_dscp_remark:
  def __init__ (self, **kw):
    self.type = ofp_meter_band_type_rev_map['OFPMBT_DSCP_REMARK']
    self.length = 0
    self.rate = 0
    self.burst_size = 0
    self.prec_level = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HHLLB3x", 
                          ofp_meter_band_type_rev_map['OFPMBT_DSCP_REMARK'],
                          self.length,
                          self.rate,
                          self.burst_size,
                          self.prec_level)
    return packed

  def unpack(self, raw, offset):
    offset,(self.type,
            self.length,
            self.rate,
            self.burst_size,
            self.prec_level) = _unpack("!HHLLB3x", raw, offset)
    return offset

  def __len__(self):
    return 16 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'type: OFPMBT_DSCP_REMARK \n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'rate: ' + str(self.rate) + '\n'
    outstr += prefix + 'burst_size: ' + str(self.burst_size) + '\n'
    outstr += prefix + 'prec_level: ' + str(self.prec_level) + '\n'
    return outstr

# experimenter - write actions in action set
class ofp_meter_band_experimenter:
  def __init__ (self, **kw):
    self.type = ofp_meter_band_type_rev_map['OFPMBT_EXPERIMENTER']
    self.length = 0
    self.rate = 0
    self.burst_size = 0
    self.experimenter = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HHLLL", 
                          self.type,
                          self.length,
                          self.rate,
                          self.burst_size,
                          self.experimenter)
    return packed

  def unpack(self, raw, offset):
    offset,(self.type,
            self.length,
            self.rate,
            self.burst_size,
            self.experimenter) = _unpack("!HHLLL", raw, offset)
    return offset

  def __len__(self):
    return 16 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'experimenter type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'rate: ' + str(self.rate) + '\n'
    outstr += prefix + 'burst_size: ' + str(self.burst_size) + '\n'
    outstr += prefix + 'prec_level: ' + str(self.prec_level) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Port Structures
# ----------------------------------------------------------------------
class ofp_port (ofp_base):
  def __init__ (self, **kw):
    self.port_no = 0
    self.hw_addr = EMPTY_ETH
    self.name = ""
    self.config = 0
    self.state = 0
    self.curr = 0
    self.advertised = 0
    self.supported = 0
    self.peer = 0
    self.curr_speed = 0
    self.max_speed = 0
    initHelper(self, kw)

  def enable_config (self, mask):
    """
    Turn on selected config bits
    """
    return self.set_config(0xffFFffFF, mask)

  def disable_config (self, mask):
    """
    Turn off selected config bits
    """
    return self.set_config(0, mask)

  def set_config (self, config, mask):
    """
    Updates the specified config bits

    Returns which bits were changed
    """
    old = self.config
    self.config &= ~mask
    self.config |= config
    return old ^ self.config
  
  # list of switch supported features from self.curr
  def curr_get_features (self):
    features = ""

    for i in range(0,15):
      if self.curr & (1 << i) != 0:
        features += ofp_port_features_map[1 << i] + ", " 

    return features

  def __str__ (self):
    return "%s:%i" % (self.name, self.port_no)

  def _validate (self):
    if isinstance(self.hw_addr, bytes) and len(self.hw_addr) == 6:
      pass
    elif not isinstance(self.hw_addr, EthAddr):
      return "hw_addr is not a valid format"
    if len(self.name) > OFP_MAX_PORT_NAME_LEN:
      return "name is too long"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!L4x", self.port_no)
    packed += (self.hw_addr if isinstance(self.hw_addr, bytes) else
               self.hw_addr.toRaw())
    packed += struct.pack("!2x")
    packed += self.name.ljust(OFP_MAX_PORT_NAME_LEN,'\0')
    packed += struct.pack("!LLLLLLLL", 
                          self.config, 
                          self.state, 
                          self.curr,
                          self.advertised, 
                          self.supported, 
                          self.peer,
                          self.curr_speed,
                          self.max_speed)
    return packed

  # unpacking of ofP-port structure 
  def unpack (self, raw, offset=0):
    _offset = offset
    offset, (self.port_no,) = _unpack("!L4x", raw, offset)

    #log.debug(binascii.hexlify(raw[offset:offset+6]))

    #offset, self.hw_addr = _readether(raw, offset)

    self.hw_addr = EthAddr(raw[offset:offset+6])
    offset += 6

    offset  += 2  # 2B padding
    offset, self.name = _readzs(raw, offset, OFP_MAX_PORT_NAME_LEN)
    offset, (self.config, 
             self.state, 
             self.curr, 
             self.advertised,
             self.supported, 
             self.peer,
             self.curr_speed,
             self.max_speed) = _unpack("!LLLLLLLL", raw, offset)

    #log.debug("offset %d - _offset %d == len(self) %d ", offset, _offset, len(self))
    assert offset - _offset == len(self)
    
    #log.debug(self.show())
    
    return offset

  @staticmethod
  def __len__ ():
    return 64

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.port_no != other.port_no: return False
    if self.hw_addr != other.hw_addr: return False
    if self.name != other.name: return False
    if self.config != other.config: return False
    if self.state != other.state: return False
    if self.curr != other.curr: return False
    if self.advertised != other.advertised: return False
    if self.supported != other.supported: return False
    if self.peer != other.peer: return False
    return True

  def __cmp__ (self, other):
    if type(other) != type(self): return id(self)-id(other)
    if self.port_no < other.port_no: return -1
    if self.port_no > other.port_no: return 1
    if self == other: return 0
    return id(self)-id(other)

  def __hash__(self, *args, **kwargs):
    return hash(self.port_no) ^ hash(self.hw_addr) ^ \
           hash(self.name) ^ hash(self.config) ^ \
           hash(self.state) ^ hash(self.curr) ^ \
           hash(self.advertised) ^ hash(self.supported) + \
           hash(self.peer)

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'port_no: ' + ofp_port_map.get(self.port_no, str(self.port_no)) + '\n'
    outstr += prefix + 'hw_addr: ' + str(EthAddr(self.hw_addr)) + '\n'
    outstr += prefix + 'name: ' + str(self.name) + '\n'
    outstr += prefix + 'config: ' + ofp_port_config_map.get(self.config, str(self.config)) +'\n'
    outstr += prefix + 'state: ' + ofp_port_state_map.get(self.state, str(self.state)) + '\n'
    outstr += prefix + 'curr: ' + self.curr_get_features() + '\n'
    outstr += prefix + 'advertised: ' + str(self.advertised) + '\n'
    outstr += prefix + 'supported: ' + str(self.supported) + '\n'
    outstr += prefix + 'peer: ' + str(self.peer) + '\n'
    outstr += prefix + 'curr_speed: ' + str(self.curr_speed) + '\n'
    outstr += prefix + 'max_speed: ' + str(self.max_speed) + '\n\n'

    return outstr

  def __repr__(self):
    return self.show()

# ----------------------------------------------------------------------
## Queue Structures
# ----------------------------------------------------------------------
class ofp_packet_queue (ofp_base):
  _MIN_LENGTH = 8
  def __init__ (self, **kw):
    self.queue_id = 0
    self.properties = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!LH", self.queue_id, len(self))
    packed += _PAD2 # Pad
    for i in self.properties:
      packed += i.pack()
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.queue_id, length) = _unpack("!LH", raw, offset)
    offset = _skip(raw, offset, 2)
    length -= (4 + 2 + 2)

    offset,self.properties = _unpack_queue_props(raw, length, offset)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    l = 8
    for i in self.properties:
      l += len(i)
    return l

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.queue_id != other.queue_id: return False
    if len(self) != len(other): return False
    if self.properties != other.properties: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'queue_id: ' + str(self.queue_id) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'properties: \n'
    for obj in self.properties:
      outstr += obj.show(prefix + '  ')
    return outstr


class ofp_queue_prop_generic (ofp_queue_prop_base):
  _MIN_LENGTH = 8
  def __init__ (self, **kw):
    self.property = None # Purposely bad
    self.data = _PAD4

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH", self.property, len(self))
    packed += self.data
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.property, length) = _unpack("!HH", raw, offset)
    offset,self.data = _read(raw, offset, length-4)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 4 + len(self.data)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.property != other.property: return False
    if len(self) != len(other): return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'property: ' + str(self.property) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    return outstr


@openflow_queue_prop('OFPQT_NONE', 0)
class ofp_queue_prop_none (ofp_queue_prop_generic):
  pass


@openflow_queue_prop('OFPQT_MIN_RATE', 1)
class ofp_queue_prop_min_rate (ofp_base):
  def __init__ (self, **kw):
    self.rate = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH", self.property, len(self))
    packed += _PAD4
    packed += struct.pack("!H", self.rate)
    packed += _PAD6
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.property, length, pad) = \
        _unpack("!HHL", raw, offset)
    offset,(self.rate,) = _unpack("!H", raw, offset)
    offset = _skip(raw, offset, 6)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.property != other.property: return False
    if self.rate != other.rate: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'property: ' + str(self.property) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'rate: ' + str(self.rate) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Flow Match Structures
# ----------------------------------------------------------------------
# TODO - check if we even use it
# ----------------------------------------------------------------------

class FlowWildcards(object):
    def __init__(self):
        self.metadata_mask = 0
        self.dl_dst_mask = 0
        self.dl_src_mask = 0
        self.vlan_vid_mask = 0
        self.ipv4_src_mask = 0
        self.ipv4_dst_mask = 0
        self.arp_spa_mask = 0
        self.arp_tpa_mask = 0
        self.arp_sha_mask = 0
        self.arp_tha_mask = 0
        self.ipv6_src_mask = []
        self.ipv6_dst_mask = []
        self.ipv6_flabel_mask = 0
        self.pbb_isid_mask = 0
        self.tunnel_id_mask = 0
        self.ipv6_exthdr_mask = 0
        self.wildcards = (1 << 64) - 1

    def ft_set(self, shift):
        self.wildcards &= ~(1 << shift)

    def ft_test(self, shift):
        return not self.wildcards & (1 << shift)

# ----------------------------------------------------------------------
# Openflow eXtensible Match (OXM)
# ----------------------------------------------------------------------
# TODO wildcarding
# ----------------------------------------------------------------------
class oxm_match_field:
  # TODO pack check
  # TODO unpack
  # TODO len check 
  def __init__(self, **kw):
    self.oxm_class = ofp_oxm_class_rev_map['OFPXMC_OPENFLOW_BASIC']
    self.oxm_field = 0
    self.oxm_hasmask = 0
    self.oxm_length = 0
    self.data = b''
    self.value = ''

    initHelper(self, kw)

  def pack(self): 
    # 7 bits are oxm_field and highest bit is oxm_hasmask 
    field = ((self.oxm_field << 1) + (self.oxm_hasmask & 1)) & 0xff

    #log.debug("self.oxm_field %d self.oxm_hasmask %d field %d", self.oxm_field, self.oxm_hasmask, field)
    
    # packing
    packed = b''
    packed += struct.pack("!HBB", 
                          self.oxm_class, 
                          field,
                          self.oxm_length,
                          )
    packed += self.data

    #log.debug("oxm_match_field packed " + binascii.hexlify(packed))

    return packed

  def __len__(self):
    #log.debug("oxm class %s field %s length %d+4 data %s", 
    #          ofp_oxm_class_map.get(self.oxm_class, "unknown "+str(self.oxm_class)),
    #          oxm_ofb_match_fields_map.get(self.oxm_field, "unknown "+str(self.oxm_field)),
    #          self.oxm_length,
    #          binascii.hexlify(self.data))

    return self.oxm_length + 4

  def show(self, prefix=''):
    """
    outstr += prefix + "oxm_field %d (%s), " % (self.oxm_field, oxm_ofb_match_fields_map[self.oxm_field] )
    outstr  = prefix + "OXM class %s (%s) \n" % (hex(self.oxm_class), ofp_oxm_class_map[self.oxm_class] )
    outstr += prefix + "oxm_hasmask %d, " % self.oxm_hasmask 
    outstr += prefix + "oxm_length %d, " % self.oxm_length
    outstr += prefix + "data " + binascii.hexlify(self.data) + '\n'
    """

    outstr  = prefix 
    outstr += "OXM field type " + oxm_ofb_match_fields_map.get(self.oxm_field, str(self.oxm_field) ) + ', '
    outstr += "OXM class " + ofp_oxm_class_map.get(self.oxm_class, str(self.oxm_class) ) + ', ' 
    outstr += ("length %d" % self.oxm_length) + ', ' 
    outstr += ("hasmask %d" % self.oxm_hasmask) + ', ' 


    if self.value == None:
      outstr += "data " + binascii.hexlify(self.data) + '\n'
    else:
      outstr += "data (value) " + str(self.value) + " data " + binascii.hexlify(self.data) +  '\n'

    return outstr


# ----------------------------------------------------------------------
# OpenFlow flow match
# ----------------------------------------------------------------------
# TODO add variables for all possible OXM unpackers 
#   (if not, we still have binary representation saved)
# TODO process the rest of OXM fields
# TODO oxm packing
# ----------------------------------------------------------------------
class ofp_match (ofp_base):
  adjust_wildcards = True # Set to true to "fix" outgoing wildcards

  def __init__ (self, **kw):
    self._locked = False
    #self._wc = FlowWildcards()
    #self._flow = Flow()

    self._in_port = 0
    self._in_phy_port = 0
    self._dl_src = EMPTY_ETH
    self._dl_dst = EMPTY_ETH
    self._dl_vlan = 0
    self._dl_vlan_pcp = 0
    self._dl_type = 0
    self._nw_tos = 0
    self._nw_proto = 0
    self._nw_src = 0
    self._nw_dst = 0
    self._tp_src = 0
    self._tp_dst = 0

    self._metadata = None
    self._type = None
    self._opcode = None
    self._arp_spa = None
    self._arp_tpa = None
    self._arp_sha = None
    self._arp_tha = None
    self._ipv6_label = None
    self._ipv6_nd_target = None
    self._ipv6_nd_sll = None
    self._ipv6_nd_tll = None
    self._ipv6_exthdr = None
    self._mpls_label = None
    self._mpls_bos = None
    self._pbb_isid = None
    self._tunnel_id = None

    self._type = OFPMT_OXM
    self._length = 4
    self._oxm_length = 0
    self._oxm_fields_pkt = []

    for k,v in ofp_match_data.iteritems():
      setattr(self, '_' + k, v)

    self.wildcards = self._normalize_wildcards(OFPFW_ALL)


    # This is basically initHelper(), but tweaked slightly since this
    # class does some magic of its own.
    for k,v in kw.iteritems():
      if not hasattr(self, '_'+k):
        raise TypeError(self.__class__.__name__ + " constructor got unexpected keyword argument '" + k + "'")
      setattr(self, k, v)
    
    self.set_oxm_from_attributes()
  
  def set_oxm_fields(self, oxms):
    self._oxm_fields_pkt = oxms
    self._length = 4 + sum(len(field) for field in self._oxm_fields_pkt)
    self._oxm_length = sum( (len(field)) for field in self._oxm_fields_pkt)
    
  def set_oxm_from_attributes(self):
    oxms = []
      
    # MAC Fields
    if self._dl_type != 0:
      oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_TYPE'],
        oxm_length = 2, data = struct.pack('!H', self._dl_type), value = ('0x' +str(self._dl_type)),))
    
    if self._dl_dst != EMPTY_ETH:
      oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_DST'],
        oxm_length = 6, data = binascii.unhexlify(self._dl_dst.toStr('', False)), value = self._dl_dst.toStr(':', False),))
    
    if self._dl_src != EMPTY_ETH:
      oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_DST'],
        oxm_length = 6, data = binascii.unhexlify(self._dl_src.toStr('', False)), value = self._dl_src.toStr(':', False),))

    # IP Fields
    if self._nw_proto != 0:
      oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IP_PROTO'],
        oxm_length = 1, data = struct.pack("!B", self._nw_proto), value = str(self._nw_proto),))  


    self.set_oxm_fields(oxms)
      
  # OF 1.2+ packing method
  def pack (self, flow_mod=False):
    """
    packing method modified to work with TLV values
    """
    assert self._assert()

    oxm_length_loc = 0

    for field in self._oxm_fields_pkt:
      #log.debug("oxm length %d data %s", field.oxm_length, binascii.hexlify(field.data))

      if field.oxm_length == 0:
        self._oxm_fields_pkt.remove(field)
      else:
        oxm_length_loc += len(field)
    
    self._length = 4 + oxm_length_loc

    #log.debug("match packing - self._length %d, len(self) %d", self._length,  len(self))

    packed = b""
    packed += struct.pack("!HH", self.type, self._length)
   
    # oxm fields
    length_oxm = self._length - 4
    _fields = self._oxm_fields_pkt   # TODO  

    for oxm_field in self._oxm_fields_pkt:
      if isinstance(oxm_field, oxm_match_field):
        packed += oxm_field.pack()

    # padding to 64 bits alignement
    length_pad = (8 - (self._length % 8)) % 8
    pad_string = "!" + str(length_pad) + "x"
    packed += struct.pack(pad_string)

    #log.debug("oxm_field packed " + binascii.hexlify(packed))

    return packed
  
  # OF 1.2+ unpacking method
  def unpack (self, raw, offset=0, flow_mod=False, match_len=0):
    _offset = offset

    offset += 4

    offset,(self._type, self._length) = _unpack("!HH", raw, offset)
    
    if (match_len != 0):
      #self._length = match_len
      length_oxm = self._length - 4
    else:
      length_oxm = self._length - 4

    self._oxm_length = length_oxm

    if(match_len > 4):
      fields = []
    else:
      fields = None

    # unpacking OXM
    while length_oxm > 0:
      offset, (oxm_class_loc, oxm_field_loc, oxm_length_loc) = _unpack("!HBB", raw, offset)
      oxm_hasmask_loc = oxm_field_loc & 1
      oxm_field_loc = oxm_field_loc >> 1
      oxm_data_value = None
      oxm_data_loc = raw[offset:offset+oxm_length_loc]

      offset += oxm_length_loc

      """
        decoding of OXM fields 
       
        decoding here should perform better than calling oxm_class object methods
      """
      if (oxm_length_loc < 1) or ((oxm_length_loc+4) > length_oxm):
        log.debug("Incorrect OXM field?? length %d+4 available %d", oxm_length_loc, length_oxm)
        length_oxm = 0

      # OFPXMT_OFB_IN_PORT 0
      elif oxm_field_loc == 0:
        (oxm_data_value,) = struct.unpack_from("!L", oxm_data_loc)
        self._in_port = oxm_data_value 
        
        #log.debug("in_port %s, in_port oxm length: %d", 
        #          ofp_port_map.get(self.in_port, hex(self.in_port)), 
        #          oxm_length_loc)
        
         
      # OFPXMT_OFB_IN_PHY_PORT 1
      elif oxm_field_loc == 1:
        (oxm_data_value,) = struct.unpack_from("!L", oxm_data_loc)
        self._in_phy_port = oxm_data_value
        #log.debug("OFPXMT_OFB_IN_PHY_PORT %d", self.in_phy_port)
        
         
      # OFPXMT_OFB_METADATA 2 
      elif oxm_field_loc == 2:
        (oxm_data_value,) = struct.unpack_from("!Q", oxm_data_loc)
        self._metadata = oxm_data_value
        #log.debug("OFPXMT_OFB_METADATA %s", binascii.hexlify(self.metadata) )


      # OFPXMT_OFB_ETH_DST 3
      elif oxm_field_loc == 3:
        oxm_data_value = ''
        for x in oxm_data_loc:
            oxm_data_value += binascii.hexlify(x)
        oxm_data_value = EthAddr(binascii.unhexlify(oxm_data_value))
        self._dl_dst = oxm_data_value
        #log.debug("L2 destination address %s", str(self.dl_dst))
      

      # OFPXMT_OFB_ETH_SRC 4
      elif oxm_field_loc == 4:
        oxm_data_value = ''
        for x in oxm_data_loc:
            oxm_data_value += binascii.hexlify(x)
        oxm_data_value = EthAddr(binascii.unhexlify(oxm_data_value))
        self._dl_src = oxm_data_value
        #log.debug("L2 source address %s", str(self.dl_src))


      # OFPXMT_OFB_ETH_TYPE 5
      elif oxm_field_loc == 5:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc) 
        self._dl_type = oxm_data_value
        #log.debug("L2 type %s (%s)", hex(self._dl_type), ethernet.l2_type_map[self.dl_type])


      # OFPXMT_OFB_VLAN_VID 6
      elif oxm_field_loc == 6:
        oxm_data_value = int(oxm_data_loc.encode('hex'), 16) # TODO check - unpacking 16 bits, specified 12+1
        self._dl_vlan = oxm_data_value 
        #log.debug("VLAN ID %d", self.dl_vlan)


      # OFPXMT_OFB_VLAN_PCP 7
      elif oxm_field_loc == 7:
        oxm_data_value = int(oxm_data_loc.encode('hex'), 16) # TODO check - unpacking 8 bits, specified 3
        self._dl_vlan_pcp = oxm_data_value 
        #log.debug("VLAN PCP %d", self.dl_vlan_pcp)


      # OFPXMT_OFB_IP_DSCP (ToS bits 0-5)  8
      elif oxm_field_loc == 8:
        oxm_data_value = int(oxm_data_loc.encode('hex'), 16) # TODO check - unpacking 8 bits, specified 6
        tos = self._nw_tos & 63
        dscp = oxm_data_value 
        self._nw_tos = int(tos+dscp)
        #log.debug("ToS: nw_tos %d from: tos_and %d dscp %d new_tos %d", self._nw_tos, tos, dscp, int(tos+dscp))


      # OFPXMT_OFB_IP_ECN (ToS bits 6-7)  9
      elif oxm_field_loc == 9:
        oxm_data_value = int(oxm_data_loc.encode('hex'), 16) # TODO check - unpacking 8 bits, specified 2
        tos = self._nw_tos & 192
        ecn = oxm_data_value 
        self._nw_tos = int(tos+ecn)
        #log.debug("ToS: nw_tos %d from: tos_and %d ecn %d new_tos %d", self._nw_tos, tos, ecn, int(tos+ecn))


      # OFPXMT_OFB_IP_PROTO 10
      elif oxm_field_loc == 10:
        (oxm_data_value,) = struct.unpack("!B", oxm_data_loc)
        self._nw_proto = oxm_data_value


      # OFPXMT_OFB_IPV4_SRC 11
      elif oxm_field_loc == 11:
        oxm_data_value = IPAddr(oxm_data_loc)
        self._nw_src = oxm_data_value
        #log.debug("OFPXMT_OFB_IPV4_SRC %d", self._nw_src)


      # OFPXMT_OFB_IPV4_DST 12
      elif oxm_field_loc == 12:
        oxm_data_value = IPAddr(oxm_data_loc)
        self._nw_dst = oxm_data_value


      # OFPXMT_OFB_TCP_SRC 13
      elif oxm_field_loc == 13:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._tp_src = oxm_data_value


      # OFPXMT_OFB_TCP_DST 14
      elif oxm_field_loc == 14:
        (oxm_data_value, ) = struct.unpack("!H", oxm_data_loc)
        self._tp_dst = oxm_data_value


      # OFPXMT_OFB_UDP_SRC 15
      elif oxm_field_loc == 15:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._tp_src = oxm_data_value


      # OFPXMT_OFB_UDP_DST 16
      elif oxm_field_loc == 16:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._tp_dst = oxm_data_value 


      # OFPXMT_OFB_SCTP_SRC 17
      elif oxm_field_loc == 17:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._tp_src = oxm_data_value


      # OFPXMT_OFB_SCTP_DST 18
      elif oxm_field_loc == 18:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._tp_dst = oxm_data_value 
        

      # OFPXMT_OFB_ICMPV4_TYPE 19
      elif oxm_field_loc == 19:
        (oxm_data_value,) = struct.unpack("!B", oxm_data_loc)
        self._opcode = oxm_data_value
        #log.debug("ICMP opcode %d", self.opcode)
        

      # OFPXMT_OFB_ICMPV4_CODE 20
      elif oxm_field_loc == 20:
        (oxm_data_value,) = struct.unpack("!B", oxm_data_loc)
        self._opcode = oxm_data_value
        #log.debug("ICMP opcode %d", self.opcode)
        

      # OFPXMT_OFB_ARP_OP 21
      elif oxm_field_loc == 21:
        (oxm_data_value,) = struct.unpack("!H", oxm_data_loc)
        self._opcode = oxm_data_value
        self.nw_proto = oxm_data_value & 0xff    # lower 8 bits 
        #log.debug("ARP opcode %d", self.opcode)


      # OFPXMT_OFB_ARP_SPA 22
      elif oxm_field_loc == 22:
        oxm_data_value = IPAddr(oxm_data_loc)
        self._arp_spa = oxm_data_value
        #log.debug("ARP IPv4 source address %s", self.arp_spa.toStr())


      # OFPXMT_OFB_ARP_TPA 23
      elif oxm_field_loc == 23:
        oxm_data_value = IPAddr(oxm_data_loc)
        self._arp_tpa = oxm_data_value
        #log.debug("ARP IPv4 target address %s", self.arp_tpa.toStr())
         

      # OFPXMT_OFB_ARP_SHA 24
      elif oxm_field_loc == 24:
        oxm_data_value = ''
        for x in oxm_data_loc:
            oxm_data_value += binascii.hexlify(x)
        oxm_data_value = EthAddr(binascii.unhexlify(oxm_data_value))
        self._arp_sha = oxm_data_value
        #log.debug("ARP source address %s", str(self.arp_sha))
      

      # OFPXMT_OFB_ARP_THA 25
      elif oxm_field_loc == 25:
        oxm_data_value = binascii.hexlify(oxm_data_loc)      # not very pretty fix
        oxm_data_value = EthAddr(binascii.unhexlify(oxm_data_value))
        self._arp_tha = oxm_data_value
        #log.debug("ARP destination address %s", str(self._arp_tpa))


      # OFPXMT_OFB_IPV6_SRC 26
      elif oxm_field_loc == 26:
        self._nw_src = IPAddr6.from_raw(oxm_data_loc)
        #log.debug("IPv6 source address %s", str(self.nw_src))

      # OFPXMT_OFB_IPV6_DST 27
      elif oxm_field_loc == 27:
        self._nw_dst = IPAddr6.from_raw(oxm_data_loc)
        #log.debug("IPv6 destination address %s", str(self.nw_dst))
       
      # OFPXMT_OFB_IPV6_FLABEL 28  # TODO check
      elif oxm_field_loc == 28:
        self._ipv6_label = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("IPv6 flow label %d", self.ipv6_label)

      # OFPXMT_OFB_ICMPV6_TYPE 29
      elif oxm_field_loc == 29:
        (oxm_data_value,) = struct.unpack("!B", oxm_data_loc)
        self._type = oxm_data_value
        #log.debug("ICMPv6 opcode %d", self.code)

      # OFPXMT_OFB_ICMPV6_CODE 30
      elif oxm_field_loc == 30:
        (oxm_data_value,) = struct.unpack("!B", oxm_data_loc)
        self._opcode = oxm_data_value
        #log.debug("ICMPv6 opcode %d", self.opcode)
      
      # OFPXMT_OFB_IPV6_ND_TARGET 31
      elif oxm_field_loc == 31:
        self._ipv6_nd_target = IPAddr6.from_raw(oxm_data_loc)
        #log.debug("IPv6 source address %s", str(self.ipv6_nd_target))

      # OFPXMT_OFB_IPV6_ND_SLL 32  # TODO check
      elif oxm_field_loc == 32:
        self._ipv6_nd_sll = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("ipv6_nd_sll %d", self.ipv6_nd_sll)


      # OFPXMT_OFB_IPV6_ND_TLL 33  # TODO check
      elif oxm_field_loc == 33:
        self._ipv6_nd_tll = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("ipv6_nd_tll %d", self.ipv6_nd_tll)


      # OFPXMT_OFB_MPLS_LABEL 34  # TODO check
      elif oxm_field_loc == 34:
        self._mpls_label = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("mpls_label %d", self.mpls_label)


      # OFPXMT_OFB_MPLS_TC 35  # TODO check
      elif oxm_field_loc == 35:
        self._mpls_tc = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("mpls_tc %d", self.mpls_tc)


      # OFPXMT_OFP_MPLS_BOS 36  # TODO check
      elif oxm_field_loc == 36:
        self._mpls_bos = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("mpls_bos %d", self.mpls_bos)


      # OFPXMT_OFB_PBB_ISID 37  # TODO check
      elif oxm_field_loc == 37:
        self._pbb_isid = int(oxm_data_loc.encode('hex'), 16)
        #log.debug("pbb_isid %d", self.pbb_isid)


      # OFPXMT_OFB_TUNNEL_ID 38
      elif oxm_field_loc == 38:
        (oxm_data_value,) = struct.unpack("!Q", oxm_data_loc)
        self.opcode = oxm_data_value
        #log.debug("ICMPv6 opcode %d", self.opcode)

      # OFPXMT_OFB_IPV6_EXTHDR 39
      elif oxm_field_loc == 39:
        self._ipv6_exthdr = int(oxm_data_loc.encode('hex'), 16)  # TODO check
        #log.debug("ipv6_exthdr %d", self.ipv6_exthdr)


      # OXM field type not processed
      else:
          oxm_data_value = None
          #log.warning("functionality for OXM field %s not implemented",
          #            oxm_ofb_match_fields_map.get(oxm_field_loc, str(oxm_field_loc)), ) 
            
      length_oxm -= (4 + oxm_length_loc)
      
      # putting data to a object
      oxm_unpacked = oxm_match_field(oxm_class = oxm_class_loc,
                                   oxm_field = oxm_field_loc,
                                   oxm_length = oxm_length_loc,
                                   oxm_hasmask = oxm_hasmask_loc,
                                   data = oxm_data_loc,
                                   value = oxm_data_value)
      fields.append(oxm_unpacked)

    # passing array of decoded classed
    self._oxm_fields_pkt = fields

    #log.debug("offset %d _offset %d match length %d offset - _offset - match_len %d", 
    #          offset,
    #          _offset,
    #          match_len,
    #          offset - _offset - match_len,)


    match_pad = (8-(match_len % 8)) % 8   # match alignment to 64-bits

    #if offset != _offset + match_len:
    #  log.debug("OXM offset %d != %d (_offset %d + match_len %d + padding %d)",
    #            offset,
    #            (_offset + match_len + match_pad),
    #            _offset,
    #            match_len,
    #            match_pad)    
      
    #assert  offset == _offset + match_len + match_pad

    return _offset + match_len + match_pad
  
  # OF1.2+ method to unpack data from Ethernet packet
  @classmethod
  def from_packet (cls, packet, in_port = None, spec_frags = False, l2_only = False):
    """
    Constructs an exact match for the given packet

    @param in_port The switch port the packet arrived on if you want
                   the resulting match to have its in_port set.
                   If "packet" is a packet_in, this is ignored.
    @param packet  A pox.packet.ethernet instance or a packet_in
    @param spec_frags Handle IP fragments as specified in the spec.
    @param l2_only New feature limiting the number of match rules by 
                   making OSI L2 matches only
    """
    if isinstance(packet, ofp_packet_in):
      in_port = packet.in_port
      packet = ethernet(packet.data)
    assert assert_type("packet", packet, ethernet, none_ok=False)

    match = cls()
    oxms = []

    # source MAC
    match._dl_src = packet.src
    oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_SRC'],
                                oxm_length = 6,
                                data = packet.src.toRaw(),
                                value = packet.src.toStr(),))
    # destination MAC
    match._dl_dst = packet.dst
    oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_DST'],
                                oxm_length = 6,
                                data = packet.dst.toRaw(),
                                value = packet.dst.toStr(),))

    # next layer ?
    match._dl_type = packet.type
    p = packet.next

    if not l2_only:
    # length specified 
      if packet.type < 1536:
        match._dl_type = OFP_DL_TYPE_NOT_ETH_TYPE

        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_TYPE'],
                                oxm_length = 2,
                                data = struct.pack("!H", OFP_DL_TYPE_NOT_ETH_TYPE),
                                value = 'OFP_DL_TYPE_NOT_ETH_TYPE',))

      # protocol specified
      else:
        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_TYPE'],
                                oxm_length = 2,
                                data = struct.pack("!H", packet.type),
                                value = str(packet.type),))

      # frame with LLC
      if isinstance(p, llc):
        if p.has_snap and p.oui == '\0\0\0':
          match._dl_type = p.eth_type
          p = p.next

      # frame with VLAN field 
      if isinstance(p, vlan):
        match._dl_type = p.eth_type

        match._dl_vlan = p.id
        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ETH_TYPE'],
                                oxm_length = 2,
                                data = struct.pack("!H", (0x1000 + (p.id & 0x0fff))),  # OFPVID_PRESENT bit + 12 bits of actual VLAN ID 
                                value = '0x1000 + '+str(p.id),))  

        match._dl_vlan_pcp = p.pcp
        p = p.next
    
      # no VLAN association
      else:
        match._dl_vlan = OFP_VLAN_NONE
        match._dl_vlan_pcp = 0

      # IPv4
      if isinstance(p, ipv4):
        match._nw_src = p.srcip
        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IPV4_SRC'],
                                oxm_length = 4,
                                data = p.srcip.toRaw(),
                                value = p.srcip.toStr(),))  

        match._nw_dst = p.dstip
        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IPV4_DST'],
                                oxm_length = 4,
                                data = p.dstip.toRaw(),
                                value = p.srcip.toStr(),))  

        match._nw_proto = p.protocol
        oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_IP_PROTO'],
                                oxm_length = 1,
                                data = struct.pack("!B", p.protocol),
                                value = str(p.protocol),))  

        match._nw_tos = p.tos
        # TODO - OXMs for DSCP and ECN - are they bit shifted in OXM or not?


        # This seems a bit strange, but see page 9 of the spec. 
        # from POX 0.3.0 so OF 1.0 - is it still necessary? TODO check
        if spec_frags and ((p.flags & p.MF_FLAG) or p.frag != 0):
          match._tp_src = 0
          match._tp_dst = 0
          return match

        # next OSI layer ? maybe :)
        p = p.next

        # TCP
        if isinstance(p, tcp):
          match._tp_src = p.srcport
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_TCP_SRC'],
                                oxm_length = 2,
                                data = struct.pack("!H", p.srcport),
                                value = str(p.srcport),))  

          match._tp_dst = p.dstport
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_TCP_DST'],
                                oxm_length = 2,
                                data = struct.pack("!H", p.dstport),
                                value = str(p.dstport),))  

        # UDP
        elif isinstance(p, udp):
          match._tp_src = p.srcport
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_UDP_SRC'],
                                oxm_length = 2,
                                data = struct.pack("!H", p.srcport),
                                value = str(p.srcport),))  

          match._tp_dst = p.dstport
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_UDP_DST'],
                                oxm_length = 2,
                                data = struct.pack("!H", p.dstport),
                                value = str(p.dstport),))  

        # ICMP
        elif isinstance(p, icmp):
          match._tp_src = p.type
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ICMPV4_TYPE'],
                                oxm_length = 1,
                                data = struct.pack("!B", p.type),
                                value = str(p.type),))  

          match._tp_dst = p.code
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ICMPV4_CODE'],
                                oxm_length = 1,
                                data = struct.pack("!B", p.code),
                                value = str(p.code),))  

      # ARP
      elif isinstance(p, arp):
        if p.opcode <= 255:
          match._nw_proto = p.opcode
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ARP_OP'],
                                oxm_length = 2,
                                data = struct.pack("!H", p.opcode),
                                value = str(p.opcode),))  

          match._nw_src = p.protosrc
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ARP_SPA'],
                                oxm_length = 4,
                                data = p.protosrc.toRaw(),
                                value = p.protosrc.toStr(),))  

          match._nw_dst = p.protodst
          oxms.append(oxm_match_field(oxm_field = oxm_ofb_match_fields_rev_map['OFPXMT_OFB_ARP_TPA'],
                                oxm_length = 4,
                                data = p.protodst.toRaw(),
                                value = p.protodst.toStr(),))  


    #log.debug("packet type %s, packet length %d in port %d", hex(packet.type), len(packet), in_port)

    match._type = OFPMT_OXM
    #match._length = 4

    match._oxm_fields_pkt = oxms
    match._length = 4 + sum(len(field) for field in match._oxm_fields_pkt)

    log.debug("match from packet length %d", match._length)

    p = packet.next

    return match
  
  # match length
  def __len__ (self):
    """
    ofp_match structure length
    1.1- - 40 octets
    1.2+ -  4 octets excluding padding (8 with padding) + length of OXM matches
    """
    self._oxm_length = sum( (len(field)) for field in self._oxm_fields_pkt)
    length_pad = (8 - ((self._oxm_length+4) % 8)) % 8

    return 4 + self._oxm_length + length_pad
    #return 8 + sum(len(field) for field in self._oxm_fields_pkt)

  def clone (self):
    n = ofp_match()
    for k,v in ofp_match_data.iteritems():
      setattr(n, '_' + k, getattr(self, '_' + k))
    n.wildcards = self.wildcards
    return n

  def flip (self, in_port = True):
    """
    Return version of this match with src and dst fields swapped

    in_port can be:
      True  : Include same in_port in new match
      Other : Set Other as in_port in new match
    """
    reversed = self.clone()
   
    if in_port is not True:
      reversed.in_port = in_port

    return reversed

  # get L3 destination address 
  def get_nw_dst (self):
    if (self.wildcards & OFPFW_NW_DST_ALL) == OFPFW_NW_DST_ALL:
      return (None, 0)

    w = (self.wildcards & OFPFW_NW_DST_MASK) >> OFPFW_NW_DST_SHIFT
    return (self._nw_dst,32-w if w <= 32 else 0)

  # get L3 source address 
  def get_nw_src (self):
    if (self.wildcards & OFPFW_NW_SRC_ALL) == OFPFW_NW_SRC_ALL:
      return (None, 0)

    w = (self.wildcards & OFPFW_NW_SRC_MASK) >> OFPFW_NW_SRC_SHIFT
    return (self._nw_src,32-w if w <= 32 else 0)

  # set L3 destination address
  def set_nw_dst (self, *args, **kw):
    a = self._make_addr(*args, **kw)
    if a is None:
      self._nw_dst = ofp_match_data['nw_dst'][0]
      self.wildcards &= ~OFPFW_NW_DST_MASK
      self.wildcards |= ofp_match_data['nw_dst'][1]
      return
    self._nw_dst = a[0]
    self.wildcards &= ~OFPFW_NW_DST_MASK
    self.wildcards |= ((32-a[1]) << OFPFW_NW_DST_SHIFT)

  # set L3 source address 
  def set_nw_src (self, *args, **kw):
    a = self._make_addr(*args, **kw)
    if a is None:
      self._nw_src = ofp_match_data['nw_src'][0]
      self.wildcards &= ~OFPFW_NW_SRC_MASK
      self.wildcards |= ofp_match_data['nw_src'][1]
      return
    self._nw_src = a[0]
    self.wildcards &= ~OFPFW_NW_SRC_MASK
    self.wildcards |= ((32-a[1]) << OFPFW_NW_SRC_SHIFT)

  def _make_addr (self, ipOrIPAndBits, bits=None):
    if ipOrIPAndBits is None: return None
    b = None
    if type(ipOrIPAndBits) is tuple:
      ip = ipOrIPAndBits[0]
      b = int(ipOrIPAndBits[1])

    if (type(ipOrIPAndBits) is str) and (len(ipOrIPAndBits) != 4):
      if ipOrIPAndBits.find('/') != -1:
        #s = ipOrIPAndBits.split('/')
        s = parse_cidr(ipOrIPAndBits, infer=False)
        ip = s[0]
        b = int(s[1]) if b is None else b
      else:
        ip = ipOrIPAndBits
        b = 32 if b is None else b
    else:
      ip = ipOrIPAndBits
      b = 32 if b is None else b

    if type(ip) is str:
      ip = IPAddr(ip)

    if bits != None: b = bits
    if b > 32: b = 32
    elif b < 0: b = 0

    return (ip, b)

  # set object attribute
  def __setattr__ (self, name, value):
    #log.debug("Setting match attribute %s", name)
    if name == '_locked':
      super(ofp_match,self).__setattr__(name, value)
      return

    if self._locked:
      raise AttributeError('match object is locked')

    if name not in ofp_match_data:
      self.__dict__[name] = value
      return

    if name == 'nw_dst' or name == 'nw_src':
      # Special handling
      getattr(self, 'set_' + name)(value)
      return value

    if value is None:
      setattr(self, '_' + name, ofp_match_data[name][0])
      self.wildcards |= ofp_match_data[name][1]
    else:
      setattr(self, '_' + name, value)
      #self.wildcards = self.wildcards & ~ofp_match_data[name][1]   # TODO check if it makes what it should - commented for purposes of debugging OXMs

    return value

  # get object attribute
  def __getattr__ (self, name):
    if name in ofp_match_data:
      """
      if ( (self.wildcards & ofp_match_data[name][1])
           == ofp_match_data[name][1] ):
        # It's wildcarded -- always return None
        return None
      """
      """
      if name == 'nw_dst' or name == 'nw_src':
        # Special handling
        return getattr(self, 'get_' + name)()[0]
      """
      return self.__dict__['_' + name]
    raise AttributeError("attribute not found: "+name)

  def _validate (self):
    # TODO
    return None

  def _prereq_warning (self):
    # Only checked when assertions are on
    if not _logger: return True
    om = self.clone()
    om.fix()

    if om == self: return True

    msg = "Fields ignored due to unspecified prerequisites: "
    #wcs = []

    for name in ofp_match_data.keys():
      if getattr(self,name) is None: continue
      if getattr(om,name) is not None: continue
      wcs.append(name)

    msg = msg + " ".join(wcs)

    _log(warn = msg)
    _log(debug = "Problematic match: " + str(self))

    return True # Always; we don't actually want an assertion error
 
  def msg_pack_into(fmt, buf, offset, *args):
    if len(buf) < offset:
        buf += bytearray(offset - len(buf))

    if len(buf) == offset:
        buf += struct.pack(fmt, *args)
        return

    needed_len = offset + struct.calcsize(fmt)
    if len(buf) < needed_len:
        buf += bytearray(needed_len - len(buf))

    struct.pack_into(fmt, buf, offset, *args) 

  def oxm_len(self):
    return self.header & 0xff

  def _normalize_wildcards (self, wildcards):
    """
    nw_src and nw_dst values greater than 32 mean the same thing as 32.
    We normalize them here just to be clean and so that comparisons act
    as you'd want them to.
    """
    if ((wildcards & OFPFW_NW_SRC_MASK) >> OFPFW_NW_SRC_SHIFT) > 32:
      wildcards &= ~OFPFW_NW_SRC_MASK
      wildcards |= (32 << OFPFW_NW_SRC_SHIFT)
    if ((wildcards & OFPFW_NW_DST_MASK) >> OFPFW_NW_DST_SHIFT) > 32:
      wildcards &= ~OFPFW_NW_DST_MASK
      wildcards |= (32 << OFPFW_NW_DST_SHIFT)
    return wildcards

  def hash_code (self):
    """
    generate a hash value for this match

    This generates a hash code which might be useful, but without locking
    the match object.
    """

    h = self.wildcards
    for f in ofp_match_data:
      v = getattr(self, f)
      if type(v) is int:
        h ^= v
      elif type(v) is long:
        h ^= v
      else:
        h ^= hash(v)

    return int(h & 0x7fFFffFF)

  def __hash__ (self):
    self._locked = True
    return self.hash_code()

  def __eq__ (self, other):
    if type(self)       != type(other): return False
    if self.in_port     != other.in_port: return False
    if self.dl_src      != other.dl_src: return False
    if self.dl_dst      != other.dl_dst: return False
    if self.dl_type     != other.dl_type: return False
    if self.nw_proto    != other.nw_proto: return False
    if self.nw_src      != other.nw_src: return False
    if self.nw_dst      != other.nw_dst: return False
    if self.tp_src      != other.tp_src: return False
    if self.tp_dst      != other.tp_dst: return False

    #new fields
    if self.type        != other.type:   return False
    if self.length      != other.length: return False
    return True

  def __str__ (self):
    return self.__class__.__name__ + "\n  " + self.show('  ').strip()
  
  def show (self, prefix=''):
    """
    OF 1.2+ show method
    """
    length_pad = (8 - ((self._oxm_length+4) % 8)) % 8

    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + (' (4 + OXM fields %d + padding %d)' % (self._oxm_length, length_pad)) + '\n'
    outstr += prefix + 'OXM length: ' + str(self._oxm_length) + '\n'
    
    # OXM fields
    for field in self._oxm_fields_pkt:
      outstr += oxm_match_field.show(field, prefix+'  ')

    #outstr += prefix + 'packed: ' + binascii.hexlify(self.pack()) + '\n'
    return outstr


# ----------------------------------------------------------------------
# OpenFlow actions
# ----------------------------------------------------------------------
# TODO the rest of actions
# ----------------------------------------------------------------------

# Base class for actions
class ofp_action_base (ofp_base):
  """
  This is sort of the equivalent of ofp_action_header in the spec.
  However, ofp_action_header as the spec defines it is not super
  useful for us, as it has the padding in it.
  """
  type = None

  @classmethod
  def unpack_new (cls, raw, offset=0):
    """
    Unpacks wire format into the appropriate action object.

    Returns newoffset,object
    """
    o = cls()
    r = o.unpack(raw, offset)
    assert (r-offset) == len(o), o
    return (r, o)

# ----------------------------------------------------------------------
# generic OF action
class ofp_action_generic (ofp_action_base):
  _MIN_LENGTH = 8
  def __init__ (self, **kw):
    self.type = None # Purposely bad

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH4x", 
                          self.type, 
                          len(self))
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, length) = _unpack("!HH4x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# action output to switch port
@openflow_action('OFPAT_OUTPUT', 0)
class ofp_action_output (ofp_action_base):
  
  def __init__ (self, **kw):
    self.port = None # Purposely bad -- require specification
    self.max_len = OFPCML_NO_BUFFER
    self.type = 0  # OFPAT_OUTPUT
    initHelper(self, kw)

  def pack (self):
    if self.port != OFPP_CONTROLLER:
      self.max_len = 0

    if self.port == None:
      log.error("OFPAT_OUTPUT: port not set !!!")

    assert self._assert()

    #log.debug(self.show())

    packed = b""
    packed += struct.pack("!HHIH6x", self.type, len(self), self.port, self.max_len)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, length, self.port, self.max_len) = \
        _unpack("!HHIH6x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if len(self) != len(other): return False
    if self.port != other.port: return False
    if self.max_len != other.max_len: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: OFPAT_OUTPUT\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'port: ' + ofp_port_map.get(self.port, hex(self.port)) + '\n'
    outstr += prefix + 'max_len: ' + str(self.max_len) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Copy TTL "outwards" -- from next-to-outermost to outermost 
@openflow_action('OFPAT_COPY_TTL_OUT', 11)
class ofp_action_copy_ttl_out (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 11

# ----------------------------------------------------------------------
# Copy TTL "inwards" -- from outermost to next-to-outermost 
@openflow_action('OFPAT_COPY_TTL_IN', 12)
class ofp_action_copt_ttl_in (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 12

# ----------------------------------------------------------------------
# MPLS TTL 
@openflow_action('OFPAT_SET_MPLS_TTL', 15)
class ofp_action_mpls_ttl (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 15
    self.len = 8
    self.mpls_ttl = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHB3x", 
                          self.type, 
                          self.len,
                          self.mpls_ttl)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len, 
            self.mpls_ttl) = _unpack("!HHB3x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.mpls_ttl != other.mpls_ttl: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'mpls ttl: ' + str(self.mpls_ttl) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Decrement MPLS TTL 
@openflow_action('OFPAT_DEC_MPLS_TTL', 16)
class ofp_action_dec_mpls_ttl (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 16

# ----------------------------------------------------------------------
# Push a new VLAN tag 
@openflow_action('OFPAT_PUSH_VLAN', 17)
class ofp_action_push_vlan (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 17
    self.len = 8
    self.ethertype = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHH2x", 
                          self.type, 
                          self.len,
                          self.ethertype)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len, 
            self.ethertype) = _unpack("!HHH2x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.ethertype != other.ethertype: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'ethertype: ' + str(self.ethertype) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Pop the outer VLAN tag 
@openflow_action('OFPAT_POP_VLAN', 18)
class ofp_action_pop_vlan (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 18

# ----------------------------------------------------------------------
# Push a new MPLS tag 
@openflow_action('OFPAT_PUSH_MPLS', 19)
class ofp_action_push_mpls (ofp_action_push_vlan):
  def __init__ (self, **kw):
    self.type = 19

# ----------------------------------------------------------------------
# Pop the outer MPLS tag 
@openflow_action('OFPAT_POP_MPLS', 20)
class ofp_action_pop_mpls (ofp_action_push_vlan):
  def __init__ (self, **kw):
    self.type = 20

# ----------------------------------------------------------------------
# Set queue id when outputting to a port 
@openflow_action('OFPAT_SET_QUEUE', 21)
class ofp_action_set_queue (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 21
    self.len = 8
    self.queue_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHL", 
                          self.type, 
                          self.len,
                          self.queue_id)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len, 
            self.queue_id) = _unpack("!HHL", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.queue_id != other.queue_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'Queue ID: ' + str(self.queue_id) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Apply group. 
@openflow_action('OFPAT_GROUP', 22)
class ofp_action_set_queue (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 22
    self.len = 8
    self.group_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHL", 
                          self.type, 
                          self.len,
                          self.group_id)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len, 
            self.group_id) = _unpack("!HHL", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.group_id != other.group_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'Group ID: ' + str(self.group_id) + '\n'
    return outstr

# ----------------------------------------------------------------------
# IP TTL. 
@openflow_action('OFPAT_SET_NW_TTL', 23)
class ofp_action_nw_ttl (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 23
    self.len = 8
    self.nw_ttl = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHB3x", 
                          self.type, 
                          self.len,
                          self.nw_ttl)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len, 
            self.nw_ttl) = _unpack("!HHB3x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.nw_ttl != other.nw_ttl: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'IPv4 TTL: ' + str(self.nw_ttl) + '\n'
    return outstr

# ----------------------------------------------------------------------
# Decrement IP TTL. 
@openflow_action('OFPAT_DEC_NW_TTL', 24)
class ofp_action_dec_nw_ttl (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 24

# ----------------------------------------------------------------------
# Set a header field using OXM TLV format. 
@openflow_action('OFPAT_SET_FIELD', 25)
class ofp_action_set_field (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 25
    self.length = 4
    self.oxm_field = None

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!H", self.type)

    # pack the correct length, OXM field and padding
    if isinstance(self.oxm_field, oxm_match_field):
      self.length = len(self.oxm_field) + 4
      packed += struct.pack("!H", self.length)
      packed += self.oxm_field.pack()
 
      pad_len = (8 - (self.length % 8)) % 8
      packed += struct.pack("!"+str(pad-len)+"x")

    else:
      packed += struct.pack("!H", self.length)

    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length) = _unpack("!HH", raw, offset)

    self.oxm_field = self.oxm_field.pack()

    pad_len = (8 - (self.length % 8)) % 8

    offset = _unpack("!"+str(pad_len)+"x", raw, offset)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return self.length

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.length != other.length: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    return outstr




# ----------------------------------------------------------------------
# Push a new PBB service tag (I-TAG) 
@openflow_action('OFPAT_PUSH_PBB', 26)
class ofp_action_push_pbb (ofp_action_push_vlan):
  def __init__ (self, **kw):
    self.type = 26

# ----------------------------------------------------------------------
# Pop the outer PBB service tag (I-TAG)
@openflow_action('OFPAT_POP_PBB', 27)
class ofp_action_pop_pbb (ofp_action_generic):
  def __init__ (self, **kw):
    self.type = 27

# ----------------------------------------------------------------------
# experimenter action 
@openflow_action('OFPAT_EXPERIMENTER', 0xffff)
class ofp_action_experimenter (ofp_action_base):
  def __init__ (self, **kw):
    self.type = 0xffff
    self.len = 4
    self.experimemter = None # ofp_experimenter_header

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH", 
                          self.type, 
                          self.len)
    # TODO pack experimenter
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.len) = _unpack("!HH", raw, offset)
    # TODO unpack experimenter
    assert offset - _offset == len(self)
    return offset

  def __len__ (self): # multiple of 8
    return 4

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.experimemter != other.experimemter: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    if self.experimemter is not None:
      outstr += prefix + 'experimemter: ' + self.experimemter.show() + '\n'
    return outstr



# ----------------------------------------------------------------------
# Base class for experimenter actions
class ofp_action_experimenter_base (ofp_action_base):

  type = 65535 # 0xffff OFPAT_EXPERIMENTER

  # Return True if equal
  # Overide this.
  def _eq (self, other):
    return True

  # Initialize fields
  # Overide this.
  def _init (self, kw):
    pass

  # Pack body.
  def _pack_body (self):
    return b""

  # Unpack body in raw starting at offset.
  # Return new offset
  def _unpack_body (self, raw, offset, avail):
    return offset
  
  # Return length of body.
  # This should include everything after the length field.
  # Optionally override this.
  def _body_length (self):
    return len(self._pack_body())

  # Format additional fields as text
  def _show (self, prefix):
    return ""

  def __init__ (self, **kw):
    self._init(kw)
    assert hasattr(self, 'experimenter')
    self.experimenter = 0
    initHelper(self, kw)

  def _pack_body (self):
    if hasattr(self.body, 'pack'):
      return self.body.pack()
    else:
      return bytes(self.body)

  def pack (self):
    assert self._assert()

    body = self._pack_body()

    packed = b""
    packed += struct.pack("!HHL", self.type, 8 + len(body), self.experimenter)
    packed += body
    assert (len(packed) % 8) == 0, "Experimenter action length not multiple of 8"
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, length, self.experimenter) = _unpack("!HHL", raw, offset)
    offset = self._unpack_body(raw, offset, length - 8)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8 + self._body_length()

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if len(self) != len(other): return False
    if self.experimenter != other.experimenter: return False
    return self._eq(other)

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'experimenter: ' + str(self.experimenter) + '\n'
    outstr += self._show(prefix)
    return outstr

# ----------------------------------------------------------------------
# experimenter action
@openflow_action('OFPAT_EXPERIMENTER', 65535)
class ofp_action_experimenter_generic (ofp_action_base):
  def __init__ (self, **kw):
    self.experimenter = 0
    self.body = b""

    initHelper(self, kw)

  def _pack_body (self):
    if hasattr(self.body, 'pack'):
      return self.body.pack()
    else:
      return bytes(self.body)

  def pack (self):
    assert self._assert()

    body = self._pack_body()

    packed = b""
    packed += struct.pack("!HHL", self.type, 8 + len(body), self.experimenter)
    packed += body
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, length, self.experimenter) = _unpack("!HHL", raw, offset)
    offset,self.body = _read(raw, offset, length - 8)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8 + len(self._pack_body())

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if len(self) != len(other): return False
    if self.experimenter != other.experimenter: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'experimenter: ' + str(self.experimenter) + '\n'
    return outstr

# ----------------------------------------------------------------------
# OpenFlow instructions 
# ----------------------------------------------------------------------
# TODO the rest of instructions
# ----------------------------------------------------------------------

# Base class for instructions
class ofp_instruction_base (ofp_base):
  type = None
  length = 4

  # Unpacks wire format into the appropriate action object.
  # Returns newoffset,object 
  @classmethod
  def unpack_new (cls, raw, offset=0):
    o = cls()
    r = o.unpack(raw, offset)
    assert (r-offset) == len(o), o
    return (r, o)

# ----------------------------------------------------------------------
# generic OF instruction
class ofp_instruction_generic (ofp_instruction_base):
  _MIN_LENGTH = 4

  def __init__ (self, **kw):
    self.type = None # Purposely bad
    self.length = 4

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH", self.type, len(self))
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length) = _unpack("!HH", raw, offset)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 4

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# OF goto table instruction
@openflow_instruction('OFPIT_GOTO_TABLE', 1)
class ofp_instruction_goto_table (ofp_instruction_base):
  _MIN_LENGTH = 8

  def __init__ (self, **kw):
    self.type = 1
    self.length = 8
    self.table_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHB3x", 
                          self.type, 
                          len(self),
                          self.table_id,)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length,
            self.table_id) = _unpack("!HHB3x", raw, offset)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.table_id != other.table_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    return outstr

# ----------------------------------------------------------------------
# OF write metadata instruction
@openflow_instruction('OFPIT_WRITE_METADATA', 2)
class ofp_instruction_write_metadata (ofp_instruction_base):
  _MIN_LENGTH = 24

  def __init__ (self, **kw):
    self.type = 2
    self.length = 24
    self.metadata = 0
    self.metadata_mask = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HH4xQQ", 
                          self.type, 
                          len(self),
                          self.metadata,
                          self.metadata_mask)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length,
            self.metadata,
            self.metadata_mask) = _unpack("!HH4xQQ", raw, offset)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 24

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.metadata != other.metadata: return False
    if self.metadata_mask != other.metadata_mask: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    outstr += prefix + 'metadata: ' + str(self.metadata) + '\n'
    outstr += prefix + 'metadata mask: ' + str(self.metadata_mask) + '\n'
    return outstr

# ----------------------------------------------------------------------
# action instructions

class ofp_instruction_actions (ofp_instruction_base):
  """
    For the Apply-Actions instruction, the actions field is treated as a list
    and the actions are applied to the packet in-order. For the Write-Actions
    instruction, the actions field is treated as a set and the actions are 
    merged into the current action set.
    
    For the Clear-Actions instruction, the structure does not contain 
    any actions.
  """
  def __init__ (self, **kw):
    self.type = None
    self.length = 0    # TODO
    self.actions = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    if self.type == None:
      log.type = 4
      log.error('Cannot determine if WRITE or APPLY ACTIONS instruction!')

    # pack actions
    actionspkd = b""
    for i in self.actions:
      if i:
        actionspkd += i.pack()

    # pack whole message
    self.length = 8 + len(actionspkd)

    packed = b""
    packed += struct.pack("!HH4x", self.type, self.length)
    packed += actionspkd

    #log.debug(self.show())

    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length) = _unpack("!HH4x", raw, offset)
    assert offset - _offset == len(self)
    
    offset, self.actions = _unpack_actions(raw,
                                          length - 8, # TODO check
                                          offset)
    return offset

  #@staticmethod
  def __len__ (self):
    actionlen = 0

    if self.actions is None:
      actionlen = 0 
    elif not self.actions:
      actionlen = 0
    elif self.actions == []:
      actionlen = 0
    else:
      for act in self.actions:
        if act:
          actionlen += len(act)

    return 8 + actionlen
  

  def __eq__ (self, other):
       if type(self) != type(other): return False
       if self.type != other.type: return False
       if len(self) != len(other): return False
       if self.port != other.port: return False
       if self.max_len != other.max_len: return False
       #if self.actions != other.actions: return False
       return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'len: ' + str(len(self)) + '\n'
    outstr += prefix + 'actions: \n'
    if self.actions:
      for obj in self.actions:
        if obj is not None:
          outstr += obj.show(prefix + '  ')
    return outstr


@openflow_instruction('OFPIT_WRITE_ACTIONS', 3)
class ofp_instruction_actions_write (ofp_instruction_actions):

  def __init__ (self, **kw):
    self.type = 3
    self.length = 0    # TODO
    self.actions = []

    initHelper(self, kw)


@openflow_instruction('OFPIT_APPLY_ACTIONS', 4)
class ofp_instruction_actions_apply (ofp_instruction_actions):

  def __init__ (self, **kw):
    self.type = 4
    self.length = 0    # TODO
    self.actions = []

    initHelper(self, kw)

@openflow_instruction('OFPIT_CLEAR_ACTIONS', 5)
class ofp_instruction_actions_clear (ofp_instruction_actions):

  def __init__ (self):
    self.type = 5
    self.length = 8
    self.actions = []

# ----------------------------------------------------------------------
# OF meter instruction
@openflow_instruction('OFPIT_METER', 6)
class ofp_instruction_meter (ofp_instruction_base):
  _MIN_LENGTH = 8

  def __init__ (self, **kw):
    self.type = 1
    self.length = 8
    self.meter_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHL", 
                          self.type, 
                          len(self),
                          self.meter_id,)
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length,
            self.meter_id) = _unpack("!HHL", raw, offset)
    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.meter_id != other.meter_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    outstr += prefix + 'meter_id: ' + str(self.meter_id) + '\n'
    return outstr

# ----------------------------------------------------------------------
# OF meter instruction
@openflow_instruction('OFPIT_EXPERIMENTER', 0xFFFF)
class ofp_instruction_experimenter (ofp_instruction_base):
  _MIN_LENGTH = 8

  def __init__ (self, **kw):
    self.type = 1
    self.length = 8
    self.experimenter = 0
    self.data = b''

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HHL", 
                          self.type, 
                          len(self),
                          self.experimenter,)
    packed += data
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,(self.type, 
            self.length,
            self.experimenter) = _unpack("!HHL", raw, offset)
    offset,self.data = _read(raw, offset, self.length - 8)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8 + len(self.data)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.type != other.type: return False
    if self.experimenter != other.experimenter: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    outstr += prefix + 'experimenter: ' + str(self.experimenter) + '\n'
    outstr += prefix + 'data: ' + binascii.hexlify(self.data) + '\n'
    return outstr

# ----------------------------------------------------------------------
# OpenFlow messages
# ----------------------------------------------------------------------
# Controller-to-Switch Messages
# ----------------------------------------------------------------------
## Features request message
# C->S
# ----------------------------------------------------------------------  
@openflow_c_message("OFPT_FEATURES_REQUEST", 
                    5, 
                    request_for="ofp_features_reply")
class ofp_features_request (ofp_header):
  """
    The controller sends a feature request to the switch upon session
    establishment.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
# Handshake
## S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_FEATURES_REPLY", 6, reply_to="ofp_features_request")
class ofp_features_reply (ofp_header):
  _MIN_LENGTH = 32
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.datapath_id = 0
    self.n_buffers = 0
    self.n_tables = 0
    self.capabilities = 0
    self.actions = 0
    self.auxiliary_id = 0
    self.ports = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!QLB", self.datapath_id, self.n_buffers,
                          self.n_tables)
    packed += _PAD3
    packed += struct.pack("!LL", self.capabilities, self.actions)
    for i in self.ports:
      packed += i.pack()
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.datapath_id, 
            self.n_buffers, 
            self.n_tables) = _unpack("!QLB", raw, offset)
    offset = _skip(raw, offset, 3)
    offset,(self.capabilities, self.actions) = _unpack("!LL", raw, offset)
    portCount = (length - 32) / len(ofp_port)
    self.ports = []
    for i in xrange(0, portCount):
      p = ofp_port()
      offset = p.unpack(raw, offset)
      self.ports.append(p)
    assert length == len(self)
    return offset,length

  def __len__ (self):
    return 32 + len(self.ports) * len(ofp_port)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.datapath_id != other.datapath_id: return False
    if self.n_buffers != other.n_buffers: return False
    if self.n_tables != other.n_tables: return False
    if self.capabilities != other.capabilities: return False
    if self.actions != other.actions: return False
    if self.ports != other.ports: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'datapath_id: ' + str(self.datapath_id) + '\n'
    outstr += prefix + 'n_buffers: ' + str(self.n_buffers) + '\n'
    outstr += prefix + 'n_tables: ' + str(self.n_tables) + '\n'
    outstr += prefix + 'capabilities: ' + str(self.capabilities) + '\n'
    outstr += prefix + 'actions: ' + str(self.actions) + '\n'
    outstr += prefix + 'ports: \n'
    for obj in self.ports:
      outstr += obj.show(prefix + '  ')
    return outstr
ofp_switch_features = ofp_features_reply

# ----------------------------------------------------------------------
## switch configuration request
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_GET_CONFIG_REQUEST", 
                    7, 
                    request_for="ofp_get_config_reply")
class ofp_get_config_request (ofp_header):
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  #def unpack (self, raw, offset=0):
  #  offset,length = self._unpack_header(raw, offset)
  #  assert length == len(self)
  #  return offset,length

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## The switch responds to a configuration request with an OFPT_GET_CONFIG_REPLY
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_GET_CONFIG_REPLY", 
                    8, 
                    reply_to="ofp_get_config_request")
class ofp_get_config_reply (ofp_header): # uses ofp_switch_config
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.flags = 0
    self.miss_send_len = OFP_DEFAULT_MISS_SEND_LEN

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HH", self.flags, self.miss_send_len)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.flags, self.miss_send_len) = \
        _unpack("!HH", raw, offset)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 12

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.flags != other.flags: return False
    if self.miss_send_len != other.miss_send_len: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'flags: ' + str(self.flags) + '\n'
    outstr += prefix + 'miss_send_len: ' + str(self.miss_send_len) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Switch Configuration
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_SET_CONFIG", 9)
class ofp_set_config (ofp_header): # uses ofp_switch_config
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.flags = 0
    self.miss_send_len = OFP_DEFAULT_MISS_SEND_LEN

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HH", self.flags, self.miss_send_len)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.flags, self.miss_send_len) = _unpack("!HH", raw, offset)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 12

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.flags != other.flags: return False
    if self.miss_send_len != other.miss_send_len: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'flags: ' + str(self.flags) + '\n'
    outstr += prefix + 'miss_send_len: ' + str(self.miss_send_len) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Modify State Messages
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_FLOW_MOD", 14)
class ofp_flow_mod (ofp_header):
  """
    Modify Flow entry message

    The controller sends this message to modify the flow table.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    cookie           Opaque controller-issued identifier
    cookie_mask      Mask used to restrict the cookie bits that must match
                     when the command is ``OPFFC_MODIFY*`` or
                     ``OFPFC_DELETE*``
    table_id         ID of the table to put the flow in
    command          One of the following values.
                     OFPFC_ADD
                     OFPFC_MODIFY
                     OFPFC_MODIFY_STRICT
                     OFPFC_DELETE
                     OFPFC_DELETE_STRICT
    idle_timeout     Idle time before discarding (seconds)
    hard_timeout     Max time before discarding (seconds)
    priority         Priority level of flow entry
    buffer_id        Buffered packet to apply to (or OFP_NO_BUFFER)
    out_port         For ``OFPFC_DELETE*`` commands, require matching
                     entries to include this as an output port
    out_group        For ``OFPFC_DELETE*`` commands, require matching
                     entries to include this as an output group
    flags            One of the following values.
                     OFPFF_SEND_FLOW_REM
                     OFPFF_CHECK_OVERLAP
                     OFPFF_RESET_COUNTS
                     OFPFF_NO_PKT_COUNTS
                     OFPFF_NO_BYT_COUNTS
    match            Instance of ``ofp_match``
    instructions     list of ``ofp_instruction`` instances
    ================ ====================================================== 
  """
  _MIN_LENGTH = 56  # with OFP header
  #_MIN_LENGTH = 48 # without OFP header
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    if 'match' in kw:
      self.match = None
    else:
      self.match = ofp_match()
    self.cookie = 0
    self.cookie_mask = 0
    self.table_id = 0
    self.command = OFPFC_ADD
    self.idle_timeout = 0
    self.hard_timeout = 0
    self.priority = OFP_DEFAULT_PRIORITY
    self._buffer_id = NO_BUFFER
    self.out_port = OFPP_CONTROLLER
    self.out_group = OFPG_ANY
    self.flags = 0
    self.instructions = None
    self.actions = None
    self.data = None # Not in the spec!  Special magic!  Can be packet_in.

    # ofp_flow_mod/ofp_packet_out do some special handling of 'actions'
    # and 'instructions'

    # Allow "action" as a synonym for "actions"
    if 'action' in kw and 'actions' not in kw:
      kw['actions'] = kw['action']
      del kw['action']

    # Allow "instruction" as a synonym for "instructions"
    if 'instruction' in kw and 'instructions' not in kw:
      kw['instructions'] = kw['instruction']
      del kw['instruction']

    initHelper(self, kw)

    # Allow use of actions=<a single action> for kw args.
    if not hasattr(self.actions, '__getitem__'):
      self.actions = [self.actions]
    
    if self.actions: 
      if self.instructions is None:
        self.instructions = []
      self.instructions.append(ofp_instruction_actions_apply(
                                actions = self.actions, 
                                type = 4, # OFPIT_APPLY_ACTION
                                ))

  @property
  def buffer_id (self):
    if self._buffer_id == NO_BUFFER: return None
    return self._buffer_id
  @buffer_id.setter
  def buffer_id (self, val):
    if val is None: val = NO_BUFFER
    self._buffer_id = val

  def _validate (self):
    if not isinstance(self.match, ofp_match):
      return "match is not class ofp_match"
    return None

  def pack (self):
    """
    Packs this object into its wire format.
    May normalize fields.
    NOTE: If "data" has been specified, this method may actually return
          *more than just a single ofp_flow_mod* in packed form.
          Specifically, it may also have a barrier and an ofp_packet_out.
    """
    po = None
    buffer_id = self.buffer_id
    if self.data:
      if not self.data.is_complete:
        _log(warn="flow_mod is trying to include incomplete data")
      else:
        self.buffer_id = self.data.buffer_id # Hacky
        if self.buffer_id is None:
          po = ofp_packet_out(data=self.data)
          po.in_port = self.data.in_port
          po.actions = [(ofp_action_output(port = OFPP_TABLE))]

          #FIXME: Should maybe check that packet hits the new entry...
          #      Or just duplicate the actions? (I think that's the best idea)
        buffer_id = self.buffer_id
        self.buffer_id = None
    
    if buffer_id is None:
      buffer_id = NO_BUFFER

    assert self._assert()
    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!QQBBHHHIIIH2x", 
                          self.cookie, 
                          self.cookie_mask,
                          self.table_id, 
                          self.command,
                          self.idle_timeout, 
                          self.hard_timeout,
                          self.priority, 
                          buffer_id, 
                          self.out_port,
                          self.out_group,
                          self.flags)
    packed += self.match.pack(flow_mod=True)
    
    # pack instructions
    if self.instructions and self.instructions is not None:
      for i in self.instructions:
          packed_loc = i.pack()
          #log.debug("flow mod - instruction type %d length %d packed %s", i.type, i.length, binascii.hexlify(packed_loc) )
          
          if (i.type == 3 or i.type == 4) and len(i) < 9:
            #log.debug("flow mod - empty action instruction")
            self.instructions.remove(i)
          else:
            packed += packed_loc

      #log.debug("flow mod - packed data %s", binascii.hexlify(packed))
    if po:
      if po.actions: 
        if self.instructions is None:
          self.instructions = [] 
        self.instructions.append(ofp_instruction_actions_apply(
                                    actions = po.actions, 
                                    type = 4, # OFPIT_APPLY_ACTION
                                    ))
    if po:
      #packed += ofp_barrier_request().pack()
      packed += po.pack()

    #log.debug(self.show())

    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.cookie, 
            self.cookie_mask,
            self.table_id,
            self.command, 
            self.idle_timeout,
            self.hard_timeout, 
            self.priority, 
            self._buffer_id,
            self.out_port, 
            self.out_group,
            self.flags) = _unpack("!QQBBHHHIII2x", raw, offset)
    offset = self.match.unpack(raw, offset, flow_mod=True)
    offset, self.instructions = _unpack_instructions(raw,
                                          length-(48 + len(self.match)), # TODO check
                                          offset)
    assert length == len(self)
    return offset, length
  
  # length
  def __len__ (self):
    matchlen = len(self.match)
    instrlen = 0

    if self.instructions and self.instructions is not None:
      for inst in self.instructions:
          if (inst.type == 3 or inst.type == 4) and len(inst) < 9:
            #log.debug("flow mod - empty action instruction")
            self.instructions.remove(inst)
          else:
            instrlen += len(inst)

    l = len(ofp_header) + 40 + matchlen + instrlen

    # log.debug("flow mod - length: %d (header %d + 40 + match %d instructions %d)", l, len(ofp_header), matchlen, instrlen)
    return l

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.match != other.match: return False
    if self.cookie != other.cookie: return False
    if self.command != other.command: return False
    if self.idle_timeout != other.idle_timeout: return False
    if self.hard_timeout != other.hard_timeout: return False
    if self.priority != other.priority: return False
    if self.buffer_id != other.buffer_id: return False
    if self.out_port != other.out_port: return False
    if self.flags != other.flags: return False
    if self.instructions != other.instructions: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'cookie: ' + str(self.cookie) + '\n'
    outstr += prefix + 'cookie_mask: ' + str(self.cookie_mask) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'command: ' + str(self.command) + '\n'
    outstr += prefix + 'idle_timeout: ' + str(self.idle_timeout) + '\n'
    outstr += prefix + 'hard_timeout: ' + str(self.hard_timeout) + '\n'
    outstr += prefix + 'priority: ' + str(self.priority) + '\n'
    outstr += prefix + 'buffer_id: ' + str(self.buffer_id) + '\n'
    outstr += prefix + 'out_port: ' + ofp_port_map.get(self.out_port, hex(self.out_port)) + '\n'
    outstr += prefix + 'out_group: ' + ofp_group_map.get(self.out_group, hex(self.out_group)) + '\n'
    outstr += prefix + 'flags: ' + str(self.flags) + '\n'

    outstr += prefix + 'match: \n'
    outstr += self.match.show(prefix + '  ')
    
    outstr += prefix + 'instructions: \n'
    for obj in self.instructions:
      outstr += obj.show(prefix + '  ')

    return outstr

# ----------------------------------------------------------------------
## Group modification message
# C->S
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_GROUP_MOD", 15)
class ofp_group_mod (ofp_header):
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.command = 0            # OFPGC_ADD
    self.type = 0               # OFPGT_ALL
    self.group_id = 0xffffffff  # OFPG_ANY
    self.buckets = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HBxL", 
                          self.port_no,
                          self.type,
                          self.group_id)

    if self.bucket:
      for bucket in self.bucket:
        packed += bucket.pack()
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.command,
            self.type,
            self.group_id) = _unpack("!HBxL", raw, offset)
    
    _length = self.length - 8

    # unpacking of one counter set per bucket
    while _length >= len(ofp_bucket):
      bucket = ofp_bucket()
      offset = ofp_bucket.unpack(bucket, raw, offset)
      _length -= len(ofp_bucket)
      self.buckets.append(bucket)

    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return len(ofp_header) + 8 + sum(len(bucket) for bucket in self.buckets)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.command != other.command: return False
    if self.group_id != other.group_id: return False
    if self.type != other.type: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'command: '  + ofp_group_mod_command.get(self.command, (self.command)) + '\n'
    outstr += prefix + 'group_id: ' + ofp_group_map.get(self.group_id, str(self.group_id)) + '\n'
    outstr += prefix + 'type: ' + ofp_group_type_map.get(self.type, str(self.type)) + '\n'

    outstr += prefix + 'buckets: \n' 
    if self.bucket:
      for bucket in self.bucket:
        outstr += bucket.show(prefix + '  ')

    return outstr

# ----------------------------------------------------------------------
## Port modification message
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_PORT_MOD", 16)
class ofp_port_mod (ofp_header):
  """
    Port modification message

    The controller sneds this message to modify the behavior of the port.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    port_no          Port number to modify
    hw_addr          The hardware address that must be the same as hw_addr
                     of ``OFPPort`` of ``OFPSwitchFeatures``
    config           Bitmap of configuration flags.
                     OFPPC_PORT_DOWN
                     OFPPC_NO_RECV
                     OFPPC_NO_FWD
                     OFPPC_NO_PACKET_IN
    mask             Bitmap of configuration flags above to be changed
    advertise        Bitmap of the following flags.
                     OFPPF_10MB_HD
                     OFPPF_10MB_FD
                     OFPPF_100MB_HD
                     OFPPF_100MB_FD
                     OFPPF_1GB_HD
                     +F_1GB_FD
                     OFPPF_10GB_FD
                     OFPPF_40GB_FD
                     OFPPF_100GB_FD
                     OFPPF_1TB_FD
                     OFPPF_OTHER
                     OFPPF_COPPER
                     OFPPF_FIBER
                     OFPPF_AUTONEG
                     OFPPF_PAUSE
                     OFPPF_PAUSE_ASYM
    ================ ======================================================
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.port_no = 0
    self.hw_addr = EMPTY_ETH
    self.config = 0
    self.mask = 0
    self.advertise = 0

    initHelper(self, kw)

  def _validate (self):
    if (not isinstance(self.hw_addr, bytes)
        and not isinstance(self.hw_addr, EthAddr)):
      return "hw_addr is not bytes or EthAddr"
    if len(self.hw_addr) != 6:
      return "hw_addr is not of size 6"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!L4x", self.port_no)
    if isinstance(self.hw_addr, bytes):
      packed += self.hw_addr
    else:
      packed += self.hw_addr.toRaw()
    packed += struct.pack("!2xLLL4x", self.config, self.mask, self.advertise)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.port_no,) = _unpack("!L2x", raw, offset)
    offset,self.hw_addr = _readether(raw, offset)
    offset,(self.config, self.mask, self.advertise) = \
        _unpack("!2xLLL4x", raw, offset)
    offset = _skip(raw, offset, 4)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 40

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.port_no != other.port_no: return False
    if self.hw_addr != other.hw_addr: return False
    if self.config != other.config: return False
    if self.mask != other.mask: return False
    if self.advertise != other.advertise: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'port_no: ' + str(self.port_no) + '\n'
    outstr += prefix + 'hw_addr: ' + str(EthAddr(self.hw_addr)) + '\n'
    outstr += prefix + 'config: ' + str(self.config) + '\n'
    outstr += prefix + 'mask: ' + str(self.mask) + '\n'
    outstr += prefix + 'advertise: ' + str(self.advertise) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Table modification message
# C->S
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_TABLE_MOD", 17)
class ofp_table_mod (ofp_header):
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.table_id = ofp_table_map['OFPTT_ALL']
    self.config = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!B3xL", 
                          self.table_id,
                          self.config)
    return packed

  def unpack (self, raw, offset=0):
    offset, length = self._unpack_header(raw, offset)

    offset, (self.table_id, 
             self.config) = _unpack("!B3xL", raw, offset)

    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return len(ofp_header) + 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.table_id != other.table_id: return False
    if self.config != other.config: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'table_id: ' + ofp_table_map.get(self.table_id, (self.table_id)) + '\n'
    outstr += prefix + 'config: ' + str(self.config) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Meter modification message
# C->S
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_METER_MOD", 29)
class ofp_meter_mod (ofp_header):
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.command = ofp_meter_mod_command_map['OFPMC_ADD']
    self.flags = 0
    self.meter_id = ofp_meter_map['OFPM_ALL']
    self.bands = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HHL", 
                          self.command,
                          self.flags,
                          self.meter_id)
    
    if self.bands:
      for band in self.bands:
        packed += band.pack()

    return packed

  def unpack (self, raw, offset=0):
    offset, length = self._unpack_header(raw, offset)

    offset, (self.command, 
             self.flags,
             self.meter_id) = _unpack("!HHL", raw, offset)

     # unpacking of meter bands
    while _length >= len(ofp_meter_band_header):
      meter_band = ofp_meter_band_header()
      offset = ofp_meter_band_header.unpack(meter_band, raw, offset)
      
      if meter_band.length < len(ofp_meter_band_header):
        _length -= len(ofp_meter_band_header)
      else:
        _length -= meter_band.length
      self.bands.append(meter_band)

    assert offset - _offset == len(self)
    return offset
  
  # list of OFPMF_* values supported
  def list_flags (flags):
    outstr = ""

    for i in range(0,3):
      if flags & (1 << i) != 0:
        outstr += ofp_meter_flags_map[1 << i] + ", "
    return outstr

  def __len__ (self):
    return len(ofp_header) + 8 + sum(len(band) for band in self.bands)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.table_id != other.table_id: return False
    if self.config != other.config: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')

    outstr += prefix + 'command: ' + ofp_meter_mod_command_map.get(self.command, (self.command)) + '\n'
    outstr += prefix + 'flags: ' + self.list_flags(self.flags) + '\n'
    outstr += prefix + 'meter_id: ' + ofp_meter_map.get(self.meter_id, str(self.meter_id)) + '\n'

    if self.bands:
      for band in self.bands:
        outstr += band.show(prefix+'  ')

    return outstr

# ----------------------------------------------------------------------
## Query for port queue configuration
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_QUEUE_GET_CONFIG_REQUEST", 22)
class ofp_queue_get_config_request (ofp_header):
  """
    Queue configuration request message

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    port             Port to be queried (OFPP_ANY to all configured queues)
    ================ ======================================================
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.port = 0
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!I4x", self.port)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.port,) = _unpack("!I4x", raw, offset)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.port != other.port: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'port: ' + str(self.port) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Queue configuration for a given port
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_QUEUE_GET_CONFIG_REPLY", 23)
class ofp_queue_get_config_reply (ofp_header):
  _MIN_LENGTH = 16
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.port = 0
    self.queues = []

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!I4x", self.port)
    for i in self.queues:
      packed += i.pack()
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.port,) = _unpack("!I4x", raw, offset)
    remaining = length - 4 - 4 - len(ofp_header)

    del self.queues[:]

    # Not tested; probably buggy
    while remaining > 0:
      q = ofp_packet_queue()
      _offset = q.unpack(raw, offset)
      l = _offset - offset
      offset = _offset
      if l < 1: raise RuntimeError("Can't parse")
      remaining -= l
      self.queues.append(q)

    assert length == len(self)
    return offset,length

  def __len__ (self):
    l = 16
    for i in self.queues:
      l += len(i)
    return l

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.port != other.port: return False
    if self.queues != other.queues: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'port: ' + str(self.port) + '\n'
    outstr += prefix + 'queues: \n'
    for obj in self.queues:
      outstr += obj.show(prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
##  Multipart messages
# ----------------------------------------------------------------------
#  multipart request
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_MULTIPART_REQUEST", 18)
class ofp_multipart_request (ofp_header):
  """
  Multipart messages are used to encode requests or replies that potentially carry 
  a large amount of data and would not always fit in a single OpenFlow message, 
  which is limited to 64KB. The request or reply is encoded as a sequence of 
  multipart messages with a specific multipart type, and re-assembled by
  the receiver. Multipart messages are primarily used to request statistics 
  or state information from the switch.

  The request is carried in one or more OFPT_MULTIPART_REQUEST messages.
  """
  _MIN_LENGTH = 16
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.type = None # Try to guess
    self.flags = 0
    self._body = b''
    self._body_packed = None # Cache

    initHelper(self, kw)

  def pack (self):
    if self.type is None:
      if isinstance(self.body, ofp_multipart_body_base):
        self.type = self.body._type
      else:
        raise RuntimeError("Can't determine body type; specify it explicitly")

    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HH4x", self.type, self.flags)
    packed += self._pack_body()
    return packed

  def _pack_body (self):
    if self._body_packed is None:
      if hasattr(self.body, 'pack'):
        self._body_packed = self._body.pack()
      else:
        self._body_packed = self._body
    return self._body_packed

  @property
  def body (self):
    return self._body
  @body.setter
  def body (self, data):
    self._body = data
    self._body_packed_cache = None

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.type, self.flags) = _unpack("!HH4x", raw, offset)
    offset,body = _read(raw, offset, length - 16)

    log.debug("Multipart request type %d (%s)",
              self.type,
              ofp_multipart_type_map[self.type])

    si = _multipart_type_to_class_info.get(self.type)
    if si is None:
      self.body = ofp_generic_multipart_body()
      self.body.unpack(body, 0, len(body))
    else:
      if si.request is None:
        raise RuntimeError("No request for " + str(si))
      self.body = si.request()
      self.body.unpack(body, 0, len(body))

      #TODO: assert entire body is unpacked
    
    log.debug(self.show()) 

    assert length == len(self)
    return offset,length

  def __len__ (self):
    return 16 + len(self._pack_body())

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.type != other.type: return False
    if self.flags != other.flags: return False
    if self._pack_body() != other._pack_body(): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'type: ' + str(self.type) + '\n'
    outstr += prefix + 'flags: ' + str(self.flags) + '\n'
    outstr += prefix + 'body:\n'
    outstr += _format_body(self.body, prefix + '  ') + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply 
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_MULTIPART_REPLY", 
                    19, 
                    reply_to="ofp_multipart_request")
class ofp_multipart_reply (ofp_header):
  """
  Multipart messages are used to encode requests or replies that potentially 
  carry a large amount of data and would not always fit in a single OpenFlow 
  message, which is limited to 64KB. The request or reply is encoded as  
  a sequence ofmultipart messages with a specific multipart type, and 
  re-assembled bythe receiver. Multipart messages are primarily used to request
  statistics or state information from the switch.

  The switch responds with one or more OFPT_MULTIPART_REPLY messages.
  """
  _MIN_LENGTH = 16
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.type = None # Guess
    self.flags = 0
    self.body = b''
    self._body_data = (None, None)

    initHelper(self, kw)

  @property
  def is_last_reply (self):
    return (self.flags & 1) == 0
  @is_last_reply.setter
  def is_last_reply (self, value):
    self.flags = self.flags & 0xfffe
    if not value:
      self.flags |= 1

  @property
  def body_data (self):
    if self._body_data[0] is not self.body:
      def _pack(b):
        return b.pack() if hasattr(b, 'pack') else b

      data = b''
      if is_listlike(self.body):
        for b in self.body:
          data += _pack(b)
      else:
        data = _pack(self.body)
      self._body_data = (self.body, data)
    return self._body_data[1]

  def pack (self):
    if self.type is None:
      if is_listlike(self.body):
        if len(self.body):
          b = self.body[0]
        else:
          b = None # Will fail below
      else:
        b = self.body
      if isinstance(b, ofp_multipart_body_base):
        self.type = b._type
      else:
        raise RuntimeError("Can't determine body type; specify it explicitly")

    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HH4x", self.type, self.flags)
    packed += self.body_data
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.type, self.flags) = _unpack("!HH4x", raw, offset)
    
    #log.debug("raw %s", binascii.hexlify(raw))

    #log.debug("Multipart reply type %d length %d offset %d", 
    #          self.type, 
    #          length, 
    #          offset)

    #offset, packed = _read(raw, offset, (length - 16))

    packed = raw[offset:(offset+length-16)]
    offset = offset+length-16

    t = _multipart_type_to_class_info.get(self.type)

    if t is None:
      #FIXME: Put in a generic container?
      self.body = packed
    else:
      if t.reply is None:
        #FIXME: Put in a generic container?
        self.body = packed
      else:
        if not t.reply_is_list:
          self.body = t.reply()
          self.body.unpack(packed, 0, len(packed))
        else:
          prev_len = len(packed)
          self.body = []
          while len(packed):
            part = t.reply()

            #log.debug("packed %s", binascii.hexlify(packed))

            off = part.unpack(packed, 0, len(packed))
            packed = packed[off:]

            #log.debug("assert len(packed) %d != prev_len %d", 
            #          len(packed), 
            #          prev_len )

            assert len(packed) != prev_len
            prev_len = len(packed)
            self.body.append(part)
    
    # log.debug(self.show() )

    # log.debug("length %d len %d len_body %d", 
    #          length, 
    #          len(self), 
    #          len(self.body) )

    assert length == len(self)
    return offset,length

  def __len__ (self):
    if isinstance(self.body, list):
      #for part in self.body:
      #  log.debug("%s - len %s", str(part), str(len(part)))
      return len(ofp_header) + 8 + sum(len(part) for part in self.body)
    return len(ofp_header) + 8 + len(self.body)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.type != other.type: return False
    if self.flags != other.flags: return False
    if self.body != other.body: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'type: ' + ofp_multipart_type_map.get(self.type, str(self.type)) + "\n"
    outstr += prefix + 'flags: ' + str(self.flags) + '\n'
    outstr += prefix + 'body:\n'
    body = self.body
    if not is_listlike(body):
      body = [body]
    for b in body:
      outstr += b.show(prefix+'  ')
    return outstr

# ----------------------------------------------------------------------
# Base class for multipart bodies
# ----------------------------------------------------------------------
class ofp_multipart_body_base (ofp_base):
  _type = None
  """
  def unpack (self, data, offset=0, avail=None):
  """

# ----------------------------------------------------------------------
# generic multipart message body
# ----------------------------------------------------------------------
class ofp_generic_multipart_body (ofp_multipart_body_base):
  _MIN_LENGTH = 0
  def __init__ (self, **kw):
    self.data = b""

    initHelper(self, kw)

  def _pack_body (self):
    if hasattr(self.data, "pack"):
      return self.data.pack()
    else:
      return self.data

  def pack (self):
    assert self._assert()

    packed += self._pack_body()
    return packed

  def unpack (self, raw, offset, avail):
    if avail is None: RuntimeError("Requires length")
    _offset = offset
    offset, self.data = _read(raw, offset, avail)
    return offset

  @staticmethod
  def __len__ ():
    return len(self._pack_body())

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'data len: ' + str(len(self.data)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# empty request body - used by several multipart messages
# ----------------------------------------------------------------------
class _empty_multipart_request_body (ofp_multipart_body_base):
  """
  OFPMP_DESC and OFPMP_TABLE have empty request bodies.  In order
  to make type guessing and unpacking consistent, we define
  classes for them anyway.
  """
  def __init__ (self, **kw):
    pass

  def pack (self):
    return b""

  def unpack (self, raw, offset, avail):
    if avail != 0:
      raise RuntimeError("Expected empty body")
    return offset

  @staticmethod
  def __len__ ():
    return 0

  def __eq__ (self, other):
    if type(self) != type(other): return False
    return True

  def show (self, prefix=''):
    return "<empty>"


# ----------------------------------------------------------------------
# 0 - OFPMP_DESC - description of OF switch 
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_DESC', 0)
class ofp_desc_multipart_request (_empty_multipart_request_body):
  """
  See _empty_multipart_request_body superclass documentation
  """
  pass
#ofp_desc_multipart_reply = ofp_desc_multipart

# ----------------------------------------------------------------------
# multipart reply - structure ofp_desc
# ----------------------------------------------------------------------
@openflow_multipart_reply("OFPMP_DESC")
class ofp_desc_multipart (ofp_multipart_body_base):
  
  def __init__ (self, **kw):
    self.mfr_desc   = ""
    self.hw_desc    = ""
    self.sw_desc    = ""
    self.serial_num = ""
    self.dp_desc    = ""

    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.mfr_desc, str):
      return "mfr_desc is not string"
    if len(self.mfr_desc) > DESC_STR_LEN:
      return "mfr_desc is not of size 256"
    if not isinstance(self.hw_desc, str):
      return "hw_desc is not string"
    if len(self.hw_desc) > DESC_STR_LEN:
      return "hw_desc is not of size 256"
    if not isinstance(self.sw_desc, str):
      return "sw_desc is not string"
    if len(self.sw_desc) > DESC_STR_LEN:
      return "sw_desc is not of size 256"
    if not isinstance(self.serial_num, str):
      return "serial_num is not string"
    if len(self.serial_num) > SERIAL_NUM_LEN:
      return "serial_num is not of size 32"
    if not isinstance(self.dp_desc, str):
      return "dp_desc is not string"
    if len(self.dp_desc) > DESC_STR_LEN:
      return "dp_desc is not of size 256"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += self.mfr_desc.ljust(DESC_STR_LEN,'\0')
    packed += self.hw_desc.ljust(DESC_STR_LEN,'\0')
    packed += self.sw_desc.ljust(DESC_STR_LEN,'\0')
    packed += self.serial_num.ljust(SERIAL_NUM_LEN,'\0')
    packed += self.dp_desc.ljust(DESC_STR_LEN,'\0')
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,self.mfr_desc   = _readzs(raw, offset, DESC_STR_LEN)
    offset,self.hw_desc    = _readzs(raw, offset, DESC_STR_LEN)
    offset,self.sw_desc    = _readzs(raw, offset, DESC_STR_LEN)
    offset,self.serial_num = _readzs(raw, offset, SERIAL_NUM_LEN)
    offset,self.dp_desc    = _readzs(raw, offset, DESC_STR_LEN)

    log.debug(self.show())

    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 1056

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.mfr_desc != other.mfr_desc: return False
    if self.hw_desc != other.hw_desc: return False
    if self.sw_desc != other.sw_desc: return False
    if self.serial_num != other.serial_num: return False
    if self.dp_desc != other.dp_desc: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'mfr_desc: ' + str(self.mfr_desc) + '\n'
    outstr += prefix + 'hw_desc: ' + str(self.hw_desc) + '\n'
    outstr += prefix + 'sw_desc: ' + str(self.sw_desc) + '\n'
    outstr += prefix + 'serial_num: ' + str(self.serial_num) + '\n'
    outstr += prefix + 'dp_desc: ' + str(self.dp_desc) + '\n'
    return outstr


# ----------------------------------------------------------------------
# 1 - OFPMP_FLOW - individual flow statistics
# ----------------------------------------------------------------------
# TODO check
# ----------------------------------------------------------------------
# multipart request - structure ofp_flow_stats
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_FLOW', 1)
class ofp_flow_multipart_request (ofp_multipart_body_base):
  """
    Individual flow statistics request message

    The controller uses this message to query individual flow statistics.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    flags            Zero or ``OFPMPF_REQ_MORE``
    table_id         ID of table to read
    out_port         Require matching entries to include this as an output
                     port
    out_group        Require matching entries to include this as an output
                     group
    cookie           Require matching entries to contain this cookie value
    cookie_mask      Mask used to restrict the cookie bits that must match
    match            Instance of ``ofp_match``
    ================ ======================================================
    """
  def __init__ (self, **kw):
    self.match = ofp_match()
    self.table_id = TABLE_ALL
    self.out_port = OFPP_ANY
    self.out_group = OFPG_ANY
    self.cookie = 0 
    self.cookie_mask = 0
 
    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.match, ofp_match):
      return "match is not class ofp_match"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!B3xII4xQQ", 
                          self.table_id, 
                          self.out_port,
                          self.out_group,
                          self.cookie,
                          self.cookie_mask)
    packed += self.match.pack()
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    
    offset,(self.table_id, 
            self.out_port,
            self.out_group,
            self.cookie,
            self.cookie_mask) = _unpack("!B3xII4xQQ", raw, offset)

    offset = self.match.unpack(raw, offset)

    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 32 + len(ofp_match)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.match != other.match: return False
    if self.table_id != other.table_id: return False
    if self.out_port != other.out_port: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'match: \n'
    outstr += self.match.show(prefix + '  ')
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'out_port: ' + str(self.out_port) + '\n'
    outstr += prefix + 'out_group: ' + str(self.out_group) + '\n'
    outstr += prefix + 'cookie: ' + str(self.cookie) + '\n'
    outstr += prefix + 'cookie_mask: ' + str(self.cookie_mask) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of ofp_flow_stats structures
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_FLOW', is_list = True)
class ofp_flow_multipart (ofp_multipart_body_base):
  """
    Individual flow statistics reply message

    The switch responds with this message to an individual flow statistics
    request.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    body             List of ``OFPFlowStats`` instance
    ================ ======================================================
    """
  _MIN_LENGTH = 56
  def __init__ (self, **kw):
    self.table_id = 0
    self.duration_sec = 0
    self.duration_nsec = 0
    self.priority = OFP_DEFAULT_PRIORITY
    self.idle_timeout = 0
    self.hard_timeout = 0
    self.cookie = 0
    self.packet_count = 0
    self.byte_count = 0
    
    # Note, in the current implementation these fields are not actually populated
    # during unpacking. Instead their length is stored in the following counters
    self.match = ofp_match()
    self.actions = []

    self.match_total_len = 0
    self.actions_total_len = 0

    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.match, ofp_match):
      return "match is not class ofp_match"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!HBx", 
                          len(self), 
                          self.table_id)
    packed += self.match.pack()
    packed += struct.pack("!LLHHH", 
                          self.duration_sec,
                          self.duration_nsec, 
                          self.priority,
                          self.idle_timeout, 
                          self.hard_timeout)
    packed += _PAD6 # Pad
    packed += struct.pack("!QQQ", 
                          self.cookie, 
                          self.packet_count,
                          self.byte_count)
    for i in self.actions:
      packed += i.pack()
    return packed
  
  # unpacking of OP
  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(length, 
            self.table_id) = _unpack("!HBx", raw, offset)
   
    offset,(self.duration_sec, 
            self.duration_nsec, 
            self.priority,
            self.idle_timeout, 
            self.hard_timeout) = _unpack("!LLHHH", raw, offset)

    offset = _skip(raw, offset, 6)
    offset,(self.cookie, 
            self.packet_count, 
            self.byte_count) = _unpack("!QQQ", raw, offset)

    # offset = self.match.unpack(raw, offset)

    offset,(match_type, match_len) = _unpack("!HH", raw, offset)
    # log.warn("unpack got match_len %s", match_len)
    offset = offset + match_len
    self.match_total_len = match_len

    offset,(instruction_type, instruction_len) = _unpack("!HH", raw, offset)
    # log.warn("unpack got instruction_len %s", instruction_len)
    offset = offset + instruction_len - 4
    self.actions_total_len = instruction_len - 4

    #assert (offset - _offset) == 48 + len(self.match)
    #offset,self.actions = _unpack_actions(raw,
    #    length - (48 + len(self.match)), offset)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return (56 + self.match_total_len + self.actions_total_len)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if len(self) != len(other): return False
    if self.table_id != other.table_id: return False
    if self.match != other.match: return False
    if self.duration_sec != other.duration_sec: return False
    if self.duration_nsec != other.duration_nsec: return False
    if self.priority != other.priority: return False
    if self.idle_timeout != other.idle_timeout: return False
    if self.hard_timeout != other.hard_timeout: return False
    if self.cookie != other.cookie: return False
    if self.packet_count != other.packet_count: return False
    if self.byte_count != other.byte_count: return False
    if self.actions != other.actions: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(len(self)) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'match: \n'
    outstr += self.match.show(prefix + '  ')
    outstr += prefix + 'duration_sec: ' + str(self.duration_sec) + '\n'
    outstr += prefix + 'duration_nsec: ' + str(self.duration_nsec) + '\n'
    outstr += prefix + 'priority: ' + str(self.priority) + '\n'
    outstr += prefix + 'idle_timeout: ' + str(self.idle_timeout) + '\n'
    outstr += prefix + 'hard_timeout: ' + str(self.hard_timeout) + '\n'
    outstr += prefix + 'cookie: ' + str(self.cookie) + '\n'
    outstr += prefix + 'packet_count: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'byte_count: ' + str(self.byte_count) + '\n'
    outstr += prefix + 'actions: \n'
    for obj in self.actions:
      outstr += obj.show(prefix + '  ')
    return outstr
ofp_flow_multipart_reply = ofp_flow_multipart


# ----------------------------------------------------------------------
# 2 - OFPMP_AGGREGATE - aggregate flow statistics
# ----------------------------------------------------------------------
# TODO check
# ----------------------------------------------------------------------
# multipart request - structure ofp_aggregate_stats_request
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_AGGREGATE', 2)
class ofp_aggregate_multipart_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.match = ofp_match()
    self.table_id = TABLE_ALL
    self.out_port = OFPP_ANY
    self.out_group = OFPG_ANY
    self.cookie = 0
    self.cookie_mask = 0

    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.match, ofp_match):
      return "match is not class ofp_match"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!BxxxLLxxxxQQ", self.table_id, self.out_port, self.out_group, self.cookie, self.cookie_mask)
    packed += self.match.pack()
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset = self.match.unpack(raw, offset)
    offset,(self.table_id, pad, self.out_port) = \
        _unpack("!BBH", raw, offset)
    assert pad == 0
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 44

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.match != other.match: return False
    if self.table_id != other.table_id: return False
    if self.out_port != other.out_port: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'match: \n'
    outstr += self.match.show(prefix + '  ')
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'out_port: ' + str(self.out_port) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - structure ofp_aggregate_stats_reply
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_AGGREGATE')
class ofp_aggregate_multipart (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.packet_count = 0
    self.byte_count = 0
    self.flow_count = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!QQL", self.packet_count, self.byte_count,
                          self.flow_count)
    packed += _PAD4 # Pad
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.packet_count, self.byte_count, self.flow_count) = \
        _unpack("!QQL", raw, offset)
    offset = _skip(raw, offset, 4)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 24

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.packet_count != other.packet_count: return False
    if self.byte_count != other.byte_count: return False
    if self.flow_count != other.flow_count: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'packet_count: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'byte_count: ' + str(self.byte_count) + '\n'
    outstr += prefix + 'flow_count: ' + str(self.flow_count) + '\n'
    return outstr
ofp_aggregate_multipart_reply = ofp_aggregate_multipart


# ----------------------------------------------------------------------
# 3 - OFPMP_TABLE - flow table statistics
# ----------------------------------------------------------------------
# TODO check
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_TABLE', 3)
class ofp_table_stats_request (_empty_multipart_request_body):
  """
  See _empty_multipart_request_body superclass documentation
  """
  pass

# ----------------------------------------------------------------------
# multipart reply - array of ofp_table_stats structures
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_TABLE', 3, is_list = True)
class ofp_table_stats (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.table_id = 0
    self.name = ""
    self.wildcards = 0
    self.max_entries = 0
    self.active_count = 0
    self.lookup_count = 0
    self.matched_count = 0

    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.name, str):
      return "name is not string"
    if len(self.name) > OFP_MAX_TABLE_NAME_LEN:
      return "name is too long"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!B", self.table_id)
    packed += _PAD3
    packed += self.name.ljust(OFP_MAX_TABLE_NAME_LEN,'\0')
    packed += struct.pack("!LLLQQ", self.wildcards, self.max_entries,
                          self.active_count, self.lookup_count,
                          self.matched_count)
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.table_id,) = _unpack("!B", raw, offset)
    offset = _skip(raw, offset, 3)
    offset,self.name = _readzs(raw, offset, OFP_MAX_TABLE_NAME_LEN)
    offset,(self.wildcards, self.max_entries, self.active_count,
            self.lookup_count, self.matched_count) = \
            _unpack("!LLLQQ", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 64

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.table_id != other.table_id: return False
    if self.name != other.name: return False
    if self.wildcards != other.wildcards: return False
    if self.max_entries != other.max_entries: return False
    if self.active_count != other.active_count: return False
    if self.lookup_count != other.lookup_count: return False
    if self.matched_count != other.matched_count: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'name: ' + str(self.name) + '\n'
    outstr += prefix + 'wildcards: ' + str(self.wildcards) + '\n'
    outstr += prefix + 'max_entries: ' + str(self.max_entries) + '\n'
    outstr += prefix + 'active_count: ' + str(self.active_count) + '\n'
    outstr += prefix + 'lookup_count: ' + str(self.lookup_count) + '\n'
    outstr += prefix + 'matched_count: ' + str(self.matched_count) + '\n'
    return outstr
ofp_table_stats_reply = ofp_table_stats


# ----------------------------------------------------------------------
# 4 - OFPMP_PORT - port statistics
# ----------------------------------------------------------------------
# TODO check
# ----------------------------------------------------------------------
# multipart request - structure ofp_port_stats_request
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_PORT", 4)
class ofp_port_multipart_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.port_no = OFPP_FLOOD
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!H", self.port_no)
    packed += _PAD6
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.port_no,) = _unpack("!H", raw, offset)
    offset = _skip(raw, offset, 6)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.port_no != other.port_no: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'port_no: ' + str(self.port_no) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of ofp_port_stats structures
# ----------------------------------------------------------------------
@openflow_multipart_reply("OFPMP_PORT", is_list = True)
class ofp_port_multipart (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.port_no = OFPP_FLOOD
    self.rx_packets = 0
    self.tx_packets = 0
    self.rx_bytes = 0
    self.tx_bytes = 0
    self.rx_dropped = 0
    self.tx_dropped = 0
    self.rx_errors = 0
    self.tx_errors = 0
    self.rx_frame_err = 0
    self.rx_over_err = 0
    self.rx_crc_err = 0
    self.collisions = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!H", self.port_no)
    packed += _PAD6
    packed += struct.pack("!QQQQQQQQQQQQ", self.rx_packets,
                          self.tx_packets, self.rx_bytes, self.tx_bytes,
                          self.rx_dropped, self.tx_dropped,
                          self.rx_errors, self.tx_errors,
                          self.rx_frame_err, self.rx_over_err,
                          self.rx_crc_err, self.collisions)
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.port_no,) = _unpack("!H", raw, offset)
    offset = _skip(raw, offset, 6)
    offset,(self.rx_packets, self.tx_packets, self.rx_bytes,
            self.tx_bytes, self.rx_dropped, self.tx_dropped,
            self.rx_errors, self.tx_errors, self.rx_frame_err,
            self.rx_over_err, self.rx_crc_err, self.collisions) = \
            _unpack("!QQQQQQQQQQQQ", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 104

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.port_no != other.port_no: return False
    if self.rx_packets != other.rx_packets: return False
    if self.tx_packets != other.tx_packets: return False
    if self.rx_bytes != other.rx_bytes: return False
    if self.tx_bytes != other.tx_bytes: return False
    if self.rx_dropped != other.rx_dropped: return False
    if self.tx_dropped != other.tx_dropped: return False
    if self.rx_errors != other.rx_errors: return False
    if self.tx_errors != other.tx_errors: return False
    if self.rx_frame_err != other.rx_frame_err: return False
    if self.rx_over_err != other.rx_over_err: return False
    if self.rx_crc_err != other.rx_crc_err: return False
    if self.collisions != other.collisions: return False
    return True

  def __add__(self, other):
    if type(self) != type(other): raise NotImplemented()
    port_no = OFPP_FLOOD
    if self.port_no == other.port_no:
      port_no = self.port_no
    return ofp_port_stats(
        port_no=port_no,
        rx_packets = self.rx_packets + other.rx_packets,
        tx_packets = self.tx_packets + other.tx_packets,
        rx_bytes = self.rx_bytes + other.rx_bytes,
        tx_bytes = self.tx_bytes + other.tx_bytes,
        rx_dropped = self.rx_dropped + other.rx_dropped,
        tx_dropped = self.tx_dropped + other.tx_dropped,
        rx_errors = self.rx_errors + other.rx_errors,
        tx_errors = self.tx_errors + other.tx_errors,
        rx_frame_err = self.rx_frame_err + other.rx_frame_err,
        rx_over_err = self.rx_over_err + other.rx_over_err,
        rx_crc_err = self.rx_crc_err + other.rx_crc_err,
        collisions = self.collisions + other.collisions)

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'port_no: ' + str(self.port_no) + '\n'
    outstr += prefix + 'rx_packets: ' + str(self.rx_packets) + '\n'
    outstr += prefix + 'tx_packets: ' + str(self.tx_packets) + '\n'
    outstr += prefix + 'rx_bytes: ' + str(self.rx_bytes) + '\n'
    outstr += prefix + 'tx_bytes: ' + str(self.tx_bytes) + '\n'
    outstr += prefix + 'rx_dropped: ' + str(self.rx_dropped) + '\n'
    outstr += prefix + 'tx_dropped: ' + str(self.tx_dropped) + '\n'
    outstr += prefix + 'rx_errors: ' + str(self.rx_errors) + '\n'
    outstr += prefix + 'tx_errors: ' + str(self.tx_errors) + '\n'
    outstr += prefix + 'rx_frame_err: ' + str(self.rx_frame_err) + '\n'
    outstr += prefix + 'rx_over_err: ' + str(self.rx_over_err) + '\n'
    outstr += prefix + 'rx_crc_err: ' + str(self.rx_crc_err) + '\n'
    outstr += prefix + 'collisions: ' + str(self.collisions) + '\n'
    return outstr
ofp_port_multipart_reply = ofp_port_multipart


# ----------------------------------------------------------------------
# 5 - OFPMP_QUEUE - queue statistics for a port
# ----------------------------------------------------------------------
# TODO check
# ----------------------------------------------------------------------
# multipart request - structure ofp_queue_stats_request
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_QUEUE", 5)
class ofp_queue_stats_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.port_no = OFPP_ALL
    self.queue_id = OFPQ_ALL

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!H", self.port_no)
    packed += _PAD2
    packed += struct.pack("!L", self.queue_id)
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.port_no,pad,self.queue_id) = _unpack("!HHL", raw, offset)
    assert pad == 0
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.port_no != other.port_no: return False
    if self.queue_id != other.queue_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'port_no: ' + str(self.port_no) + '\n'
    outstr += prefix + 'queue_id: ' + str(self.queue_id) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of ofp_queue statistics
# ----------------------------------------------------------------------
@openflow_multipart_reply("OFPMP_QUEUE", is_list = True)
class ofp_queue_stats (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.port_no = 0
    self.queue_id = 0
    self.tx_bytes = 0
    self.tx_packets = 0
    self.tx_errors = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("!H", self.port_no)
    packed += _PAD2
    packed += struct.pack("!LQQQ", self.queue_id, self.tx_bytes,
                          self.tx_packets, self.tx_errors)
    return packed

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.port_no, pad, self.queue_id, self.tx_bytes,
            self.tx_packets, self.tx_errors) = \
            _unpack("!HHLQQQ", raw, offset)
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 32

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.port_no != other.port_no: return False
    if self.queue_id != other.queue_id: return False
    if self.tx_bytes != other.tx_bytes: return False
    if self.tx_packets != other.tx_packets: return False
    if self.tx_errors != other.tx_errors: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'port_no: ' + str(self.port_no) + '\n'
    outstr += prefix + 'queue_id: ' + str(self.queue_id) + '\n'
    outstr += prefix + 'tx_bytes: ' + str(self.tx_bytes) + '\n'
    outstr += prefix + 'tx_packets: ' + str(self.tx_packets) + '\n'
    outstr += prefix + 'tx_errors: ' + str(self.tx_errors) + '\n'
    return outstr
ofp_queue_stats_reply = ofp_queue_stats


# ----------------------------------------------------------------------
# 6 - OFPMP_GROUP - Group counter statistics.
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - struct ofp_group_stats_request.
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_GROUP", 6)
class ofp_group_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.group_id = OFPG_ALL

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("L4x", self.group_id)
    return packed

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    
    return True

  def show (self, prefix=''):
    outstr = prefix + 'group_id: ' + ofp_group_map.get(self.group_id, str(self.group_id)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of struct ofp_group_stats.
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_GROUP', is_list = True)
class ofp_group (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.length = 0
    self.group_id = OFPG_ALL
    self.ref_count = 0
    self.packet_count = 0
    self.byte_count = 0
    self.duration_sec = 0
    self.duration_nsec = 0
    self.bucket_stats = []

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.length, # length of this entry
            self.group_id,
            self.ref_count,
            self.packet_count,
            self.byte_count,
            self.duration_sec,
            self.duration_nsec) = _unpack("!H2xLL4xQQLL", raw, offset)
    
    _length = self.length - 40

    # unpacking of one counter set per bucket
    while _length >= len(ofp_bucket_counter):
      bucket_counter = ofp_bucket_counter()
      offset = ofp_bucket_counter.unpack(bucket_counter, raw, offset)
      _length -= len(ofp_bucket_counter)
      self.bucket_stats.append(bucket_counter)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 40 + sum(len(bstat) for bstat in self.bucket_stats)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.length != other.length: return False
    if self.group_id != other.group_id: return False
    if self.ref_count != other.ref_count: return False
    if self.packet_count != other.packet_count: return False
    if self.byte_count != other.byte_count: return False
    if self.duration_sec != other.duration_sec: return False
    if self.duration_nsec != other.duration_nsec: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'group_id: ' + ofp_group_map.get(self.group_id, str(self.group_id)) + '\n'
    outstr += prefix + 'ref_count: ' + str(self.ref_count) + '\n'
    outstr += prefix + 'packet_count: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'byte_count: ' + str(self.byte_count) + '\n'
    outstr += prefix + 'duration_sec: ' + str(self.duration_sec) + '\n'
    outstr += prefix + 'duration_nsec: ' + str(self.duration_nsec) + '\n'

    outstr += prefix + 'bucket counter stats: \n' 
    if self.bucket_stats:
      for bs in self.bucket_stats:
        outstr += bs.show() + '\n'

    return outstr
ofp_group_reply = ofp_group


# ----------------------------------------------------------------------
# 7 - OFPMP_GROUP_DESC - Group description.
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_GROUP_DESC', 7)
class ofp_group_desc_request (_empty_multipart_request_body):
  pass


# ----------------------------------------------------------------------
# multipart reply - array of struct ofp_group_desc.
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_GROUP_DESC', is_list = True)
class ofp_group_desc (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.length = 0
    self.type = 0       # OFPGT_ALL
    self.group_id = 0
    self.buckets = []

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.length, # length of this entry
            self.type,
            group_id) = _unpack("!HBxL", raw, offset)
    
    _length = self.length - 8

    # unpacking of one counter set per bucket
    while _length >= len(ofp_bucket):
      bucket = ofp_bucket()
      offset = ofp_bucket.unpack(bucket, raw, offset)
      _length -= len(ofp_bucket)
      self.buckets.append(bucket)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8 + sum(len(bucket) for bucket in self.buckets)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.length != other.length: return False
    if self.group_id != other.group_id: return False
    if self.type != other.type: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'group_id: ' + ofp_group_map.get(self.group_id, str(self.group_id)) + '\n'
    outstr += prefix + 'type: ' + ofp_group_type_map.get(self.type,str(self.type)) + '\n'

    outstr += prefix + 'buckets: \n' 
    if self.bucket:
      for bucket in self.bucket:
        outstr += bucket.show(prefix + '  ')

    return outstr
ofp_group_desc_reply = ofp_group_desc


# ----------------------------------------------------------------------
# 8 - OFPMP_GROUP_FEATURES - Group features
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_GROUP_FEATURES', 8)
class ofp_group_features_request (_empty_multipart_request_body):
  pass

# ----------------------------------------------------------------------
# multipart reply - struct ofp_group_features
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_GROUP_FEATURES')
class ofp_group_features (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.types = 0
    self.capabilities = 0

    self.max_groups0 = 0
    self.max_groups1 = 0
    self.max_groups2 = 0
    self.max_groups3 = 0

    self.actions0 = 0
    self.actions1 = 0
    self.actions2 = 0
    self.actions3 = 0

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.types,
            self.capabilities,
            self.max_groups0,
            self.max_groups1,
            self.max_groups2,
            self.max_groups3,
            self.actions0,
            self.actions1,
            self.actions2,
            self.actions3,) = _unpack("!LL4L4L", raw, offset)
    
    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ ():
    return 40

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.types != other.types: return False
    if self.capabilities != other.capabilities: return False
    if self.max_groups0 != other.max_groups0: return False
    if self.max_groups1 != other.max_groups1: return False
    if self.max_groups2 != other.max_groups2: return False
    if self.max_groups3 != other.max_groups3: return False
    if self.actions0 != other.actions0: return False
    if self.actions1 != other.actions1: return False
    if self.actions2 != other.actions2: return False
    if self.actions3 != other.actions3: return False
    return True

  # list of OFPGT_* values supported
  def list_types (types):
    outstr = ""

    for i in range(0,3):
      if types & (1 << i) != 0:
        outstr += ofp_group_type_map[i] + ", "
    return outstr

  # list of OFPGFC_* capabilities supported
  def list_group_capabilities (capabilities):
    outstr = ""

    for i in range(0,3):
      if capabilities & (1 << i) != 0:
        outstr += ofp_group_capabilities_map[1 << i] + ", "
    return outstr

  # list of OFPAT_* actions supported
  def list_group_capabilities (actions):
    outstr = ""

    for i in range(0,27):
      if actions & (1 << i) != 0:
        outstr += ofp_action_type_map.get(i, str(i)) + ", "
    return outstr

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'types: ' + self.list_types(self.types) + '\n'
    outstr += prefix + 'capabilities: ' + self.list_group_capabilities(self.capabilities) + '\n'

    outstr += prefix + 'max groups[0]: ' + self.max_groups0 + '\n'
    outstr += prefix + 'max groups[1]: ' + self.max_groups1 + '\n'
    outstr += prefix + 'max groups[2]: ' + self.max_groups2 + '\n'
    outstr += prefix + 'max groups[3]: ' + self.max_groups3 + '\n'
     
    outstr += prefix + 'actions[0]: ' + self.list_group_capabilities(self.actions0) + '\n'
    outstr += prefix + 'actions[1]: ' + self.list_group_capabilities(self.actions1) + '\n'
    outstr += prefix + 'actions[2]: ' + self.list_group_capabilities(self.actions2) + '\n'
    outstr += prefix + 'actions[3]: ' + self.list_group_capabilities(self.actions3) + '\n'

    return outstr
ofp_group_features_reply = ofp_group_features


# ----------------------------------------------------------------------
# 9 - OFPMP_METER - Meter statistics.
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - struct ofp_meter_multipart_requests
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_METER", 9)
class ofp_meter_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.meter_id = ofp_meter_rev_map['OFPM_ALL']

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("L4x", self.meter_id)
    return packed

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.meter_id != other.meter_id: return False
    return True

  def show (self, prefix=''):
    outstr = prefix + 'meter_id: ' + ofp_meter_map.get(self.meter_id, str(self.meter_id)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of struct ofp_meter_stats
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_METER', is_list = True)
class ofp_meter (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.meter_id = ofp_meter_rev_map['OFPM_ALL']
    self.length = 0
    self.flow_count = 0
    self.packet_in_count = 0
    self.byte_in_count = 0
    self.duration_sec = 0
    self.duration_nsec = 0
    self.band_stats = []

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.meter_id,
            self.length, # length of this entry
            self.flow_count,
            self.packet_in_count,
            self.byte_in_count,
            self.duration_sec,
            self.duration_nsec) = _unpack("!LH6xLQQLL", raw, offset)
    
    _length = self.length - 40

    # unpacking of statistics for each meter band
    while _length >= len(ofp_meter_band_stats):
      meter_band = ofp_meter_band_stats()
      offset = ofp_meter_band_stats.unpack(meter_band, raw, offset)
      _length -= len(ofp_meter_band_stats)
      self.band_stats.append(meter_band)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 40 + sum(len(bstat) for bstat in self.band_stats)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.length != other.length: return False
    if self.meter_id != other.meter_id: return False
    if self.flow_count != other.flow_count: return False
    if self.packet_in_count != other.packet_in_count: return False
    if self.byte_in_count != other.byte_in_count: return False
    if self.duration_sec != other.duration_sec: return False
    if self.duration_nsec != other.duration_nsec: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'meter_id: ' + ofp_group_map.get(self.meter_id, str(self.meter_id)) + '\n'
    outstr += prefix + 'flow_count: ' + str(self.flow_count) + '\n'
    outstr += prefix + 'packet_in_count: ' + str(self.packet_in_count) + '\n'
    outstr += prefix + 'byte_in_count: ' + str(self.byte_in_count) + '\n'
    outstr += prefix + 'duration_sec: ' + str(self.duration_sec) + '\n'
    outstr += prefix + 'duration_nsec: ' + str(self.duration_nsec) + '\n'

    outstr += prefix + 'meter band counter stats: \n' 
    if self.band_stats:
      for bs in self.band_stats:
        outstr += bs.show() + '\n'

    return outstr
ofp_meter_reply = ofp_meter


# ----------------------------------------------------------------------
# 10 - OFPMP_METER_CONFIG - Meter configuration.
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - struct ofp_meter_multipart_requests.
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_METER_CONFIG", 10)
class ofp_meter_config_request (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.meter_id = ofp_meter_rev_map['OFPM_ALL']

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += struct.pack("L4x", self.meter_id)
    return packed

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.meter_id != other.meter_id: return False
    return True

  def show (self, prefix=''):
    outstr = prefix + 'meter_id: ' + ofp_meter_map.get(self.meter_id, str(self.meter_id)) + '\n'
    return outstr

# ----------------------------------------------------------------------
# multipart reply - array of struct ofp_meter_config.
# ----------------------------------------------------------------------
# TODO - check if ofp_meter_band_header isn't followed by appropriate band
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_METER_CONFIG', is_list = True)
class ofp_meter_config (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.meter_id = ofp_meter_rev_map['OFPM_ALL']
    self.length = 0
    self.flags = 0
    self.bands = []

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.length, # length of this entry
            self.flags,
            self.meter_id) = _unpack("!HHL", raw, offset)
    
    _length = self.length - 8

    # unpacking of statistics for each meter band
    while _length >= len(ofp_meter_band_header):
      meter_band = ofp_meter_band_header()
      offset = ofp_meter_band_header.unpack(meter_band, raw, offset)
      
      if meter_band.length < len(ofp_meter_band_header):
        _length -= len(ofp_meter_band_header)
      else:
        _length -= meter_band.length
      self.bands.append(meter_band)

    assert offset - _offset == len(self)
    return offset

  def __len__ (self):
    return 8 + sum(bstat.length for bstat in self.bands)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.length != other.length: return False
    if self.meter_id != other.meter_id: return False
    if self.flow_count != other.flow_count: return False

    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'meter_id: ' + ofp_group_map.get(self.meter_id, str(self.meter_id)) + '\n'
    outstr += prefix + 'flow_count: ' + str(self.flow_count) + '\n'

    outstr += prefix + 'meter bands: \n' 
    if self.band_stats:
      for bs in self.bands:
        outstr += bs.show(prefix+'  ') + '\n'

    return outstr
ofp_meter_config_reply = ofp_meter_config


# ----------------------------------------------------------------------
# 11 - OFPMP_METER_FEATURES - Meter features.
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_METER_FEATURES', 11)
class ofp_meter_features_request (_empty_multipart_request_body):
  pass

# ----------------------------------------------------------------------
# multipart reply - struct ofp_meter_features.
# ----------------------------------------------------------------------
# TODO unpack bitmaps
# ----------------------------------------------------------------------
@openflow_multipart_reply('OFPMP_METER_FEATURES')
class ofp_meter_features (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.max_meters = 0
    self.band_types = 0
    self.capabilities = 0
    self.max_bands = 0
    self.max_color = 0

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.max_meters,
            self.band_types,
            self.capabilities,
            self.max_bands,
            self.max_color,) = _unpack("!LLBB2x", raw, offset)

    assert offset - _offset == len(self)
    return offset

  @staticmethod
  def __len__ (self):
    return 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.max_meters != other.max_meters: return False
    if self.band_types != other.band_types: return False
    if self.capabilities != other.capabilities: return False
    if self.max_bands != other.max_bands: return False
    if self.max_color != other.max_color: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'max_meters: ' + str(self.max_meters) + '\n'
    outstr += prefix + 'band_types: ' + str(self.band_types) + '\n'
    outstr += prefix + 'capabilities: ' + str(self.capabilities) + '\n'
    outstr += prefix + 'max_bands: ' + str(self.max_bands) + '\n'
    outstr += prefix + 'max_color: ' + str(self.max_color) + '\n'

    return outstr
ofp_meter_features_reply = ofp_meter_features


# ----------------------------------------------------------------------
# 12 - OFPMP_TABLE_FEATURES - Table features.
# ----------------------------------------------------------------------
# multipart request - either empty 
#    or contains an array of struct ofp_table_features containing 
#    the controller's desired view of the switch. 
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_TABLE_FEATURES', 12)
class ofp_port_desc_request (_empty_multipart_request_body):
  pass


# ----------------------------------------------------------------------
# multipart reply - array of struct ofp_table_features
# ----------------------------------------------------------------------
# TODO properties - unpack as appropriate type .. or find out what to do with them :)
# ----------------------------------------------------------------------
# Common header for all Table Feature Properties
class ofp_table_feature_prop_header:
  def __init__ (self, **kw):
    self.type = 0
    self.length = 0

    initHelper(self, kw)

  def pack (self):
    packed  = b''
    packed += struct.pack("HH", 
                          self.type,
                          self.length)
    return packed

  def unpack(self, raw, offset):
    offset,(self.type,
            self.length) = _unpack("!HHLL", raw, offset)
    return offset

  def __len__(self):
    return 4 

  def show(self, prefix=''):
    outstr  = ''
    outstr += prefix + 'type: ' + ofp_table_feature_prop_type_map.get(self.type, str(self.type)) + '\n'
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'data: \n'
    # property data
    return outstr

# reply message
@openflow_multipart_reply('OFPMP_TABLE_FEATURES', is_list = True)
class ofp_table_features (ofp_multipart_body_base):
  def __init__ (self, **kw):
    self.length = 0
    self.table_id = 0
    self.name = ""
    self.metadata_match = 0
    self.metadata_write = 0
    self.config = 0
    self.max_entries = 0
    self.properties = []

    initHelper(self, kw)

  def unpack (self, raw, offset, avail):
    _offset = offset
    offset,(self.length, # length of this entry
            self.table_id) = _unpack("!HB5x", raw, offset)
    
    offset, self.name = _readzs(raw, offset, OFP_MAX_TABLE_NAME_LEN)
   
    offset,(self.metadata_match,
            self.metadata_write,
            self.config,
            self.max_entries,) = _unpack("!QQLL", raw, offset)
    
    _length = self.length - 64

    # unpacking of statistics for each meter band
    while _length >= len(ofp_table_feature_prop_header):
      property = ofp_table_feature_prop_header()
      offset = ofp_table_feature_prop_header.unpack(property, raw, offset)
      
      if property.length < len(ofp_table_feature_prop_header):
        _length -= len(ofp_table_feature_prop_header)
      else:
        _length -= property.length
      self.properties.append(property)

    assert offset - _offset == len(self)
    return offset


  def __len__ ():
    return 64 + sum(property.length for property in self.properties)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.length != other.length: return False
    if self.table_id != other.table_id: return False
    if self.name != other.name: return False
    if self.metadata_match != other.metadata_match: return False
    if self.metadata_write != other.metadata_write: return False
    if self.config != other.config: return False
    if self.max_entries != other.max_entries: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'length: ' + str(self.length) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'name: ' + str(self.name) + '\n'
    outstr += prefix + 'metadata_match: ' + str(self.metadata_match) + '\n'
    outstr += prefix + 'metadata_write: ' + str(self.metadata_write) + '\n'
    outstr += prefix + 'config: ' + str(self.config) + '\n'
    outstr += prefix + 'max_entries: ' + str(self.max_entries) + '\n'
    
    if self.properties:
      outstr += prefix + 'properties: \n'
      for property in self.properties:
        outstr += property.show(prefix+'  ') + '\n'

    return outstr
ofp_table_features_reply = ofp_table_features


# ----------------------------------------------------------------------
# 13 - OFPMP_PORT_DESC - port description
# ----------------------------------------------------------------------
# multipart request - empty body
# ----------------------------------------------------------------------
@openflow_multipart_request('OFPMP_PORT_DESC', 13)
class ofp_port_desc_request (_empty_multipart_request_body):
  pass

# ----------------------------------------------------------------------
# multipart reply - array of ofp_port structures
# ----------------------------------------------------------------------
@openflow_multipart_reply("OFPMP_PORT_DESC", is_list = True)
class ofp_port_desc_reply(ofp_port):
  def unpack (self, raw, offset, avail):
    return ofp_port.unpack(self, raw, offset)


# ----------------------------------------------------------------------
# 0xffff - OFPMP_EXPERIMENTER - experimenter extension
# ----------------------------------------------------------------------
# TODO test
# ----------------------------------------------------------------------
# multipart request - begin with structure ofp_experimenter_multipart_header
#                   - the rest of body is experimenter-defined
# ----------------------------------------------------------------------
@openflow_multipart_request("OFPMP_EXPERIMENTER", 0xffff, is_list = False)

# ----------------------------------------------------------------------
# multipart reply - begin with structure ofp_experimenter_multipart_header
#                 - the rest of body is experimenter-defined
# ----------------------------------------------------------------------
@openflow_multipart_reply("OFPMP_EXPERIMENTER", 0xffff, is_list = False)
class ofp_experimenter_multipart_generic (ofp_multipart_body_base):
  _MIN_LENGTH = 4
  def __init__ (self, **kw):
    self.experimenter = None
    self.data = b""

    initHelper(self, kw)

  def _pack_body (self):
    if hasattr(self.data, "pack"):
      return self.data.pack()
    else:
      return self.data

  def pack (self):
    assert self._assert()

    packed = struct.pack("!L", self.experimenter)
    packed += self._pack_body()
    return packed

  def unpack (self, raw, offset, avail):
    if avail is None: RuntimeError("Requires length")
    _offset = offset
    offset,(self.experimenter,) = _unpack("!L", raw, offset)
    offset,self.data = _read(raw, offset, avail-4)
    return offset

  @staticmethod
  def __len__ ():
    return 4+len(self._pack_body())

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if self.experimenter != other.experimenter: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'experimenter id: ' + str(self.experimenter) + '\n'
    outstr += prefix + 'data len: ' + str(len(self.data)) + '\n'
    return outstr


# ----------------------------------------------------------------------
## Packet-Out message
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_PACKET_OUT", 13)
class ofp_packet_out (ofp_header):
  """
    The controller uses this message to send a packet out throught the
    switch.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    buffer_id        ID assigned by datapath (OFP_NO_BUFFER if none)
    in_port          Packet's input port or ``OFPP_CONTROLLER``
    actions          list of OpenFlow action class
    data             Packet data
    ================ ======================================================
  """
  _MIN_LENGTH = 24
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self._buffer_id = NO_BUFFER
    self.in_port = OFPP_CONTROLLER
    self.actions = []
    self._data = b''

    # ofp_flow_mod & ofp_packet_out do some special handling of 'actions'

    # Allow "action" as a synonym for "actions"
    if 'action' in kw and 'actions' not in kw:
      kw['actions'] = kw['action']
      del kw['action']
    initHelper(self, kw)

    # Allow use of actions=<a single action> for kw args.
    if not hasattr(self.actions, '__getitem__'):
      self.actions = [self.actions]

  @property
  def buffer_id (self):
    if self._buffer_id == NO_BUFFER: return None
    return self._buffer_id
  @buffer_id.setter
  def buffer_id (self, val):
    if val is None: val = NO_BUFFER
    self._buffer_id = val

  @property
  def data (self):
    return self._data

  @data.setter
  def data (self, data):
    if data is None:
      self._data = b''
    elif isinstance(data, packet_base):
      self._data = data.pack()
    elif isinstance(data, ofp_packet_in):
      # Enable you to easily resend a packet
      self._data = b''
      self.buffer_id = data.buffer_id
      if self.buffer_id is None:
        #TODO: It'd be nice to log and then ignore if data is incomplete
        #      Unfortunately, we currently have no logging in here, so we
        #      assert instead which is a either too drastic or too quiet.
        assert data.is_complete
        self._data = data._data
      self.in_port = data.in_port
    elif isinstance(data, bytes):
      self._data = data
    assert assert_type("data", self._data, (bytes,))

  def _validate (self):
    if self.buffer_id is not None and self.data != b'':
      return "can not have both buffer_id and data set"
    return None
  
  # packet out packing method - primary functionality
  def pack (self):
    assert self._assert()

    # we need the actions size
    action_len = 0
    if self.actions:
      actions = b''.join((i.pack() for i in self.actions))
      actions_len = len(actions)

    # mandatory fields
    #log.debug("self._buffer_id %s, self.in_port %s, actions_len %s", 
    #          str(self._buffer_id), 
    #          str(self.in_port), 
    #          str(actions_len),)

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!LLH6x", self._buffer_id, self.in_port, actions_len)
    
    # ofp actions
    if not self.actions or self.actions == None: 
      #log.debug("packet out - adding output action")
      self.actions = [ofp_action_output(type = OFPAT_OUTPUT, port = OFPP_FLOOD)] 

    if self.actions:
      packed += actions
      #log.debug("packet out - actions present: " + binascii.hexlify(self.actions))
    
    # whole packet 
    if self.data and self.data is not None:
      packed += self.data
   
    """
    log.debug("len(self) %d, length calculated %d, len actions %d, len data %d", 
              len(self), 
              (len(ofp_header)+16+len(actions)+len(self.data)), 
              len(actions), 
              len(self.data) )
    """

    # log.debug(self.show())

    return packed

  # packet out unpacking method - needed?
  def unpack (self, raw, offset=0):
    _offset = offset
    offset,length = self._unpack_header(raw, offset)
    offset,(self._buffer_id, self.in_port, actions_len) = \
        _unpack("!LLH6x", raw, offset)
    offset,self.actions = _unpack_actions(raw, actions_len, offset)

    remaining = length - (offset - _offset)
    if remaining <= 0:
      self.data = None
    else:
      offset,self.data = _read(raw, offset, remaining)

    assert length == len(self)
    return offset,length

  def __len__ (self):
    #return 16 + reduce(operator.add, (len(a) for a in self.actions), 0)
    #          + (len(self.data) if self.data else 0)
    
    actions = b''.join((i.pack() for i in self.actions))
    return ( len(ofp_header) + 16 + len(actions) + len(self.data) )

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.buffer_id != other.buffer_id: return False
    if self.in_port != other.in_port: return False
    if self.actions != other.actions: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'buffer_id: ' + str(self.buffer_id) + '\n'
    outstr += prefix + 'in_port: ' + str(self.in_port) + '\n'
    outstr += prefix + 'actions_len: ' + str(len(self.actions)) + '\n'
    outstr += prefix + 'actions: \n'
    for obj in self.actions:
      if obj is None:
        raise RuntimeError("An element of self.actions was None! " +
                           "Bad formatting...")
      outstr += obj.show(prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## Barrier Message
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_BARRIER_REPLY", 21, reply_to="ofp_barrier_request")
class ofp_barrier_reply (ofp_header):
  """
    Barrier reply message

    The switch responds with this message to a barrier request.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  #def unpack (self, raw, offset=0):
  #  offset,length = self._unpack_header(raw, offset)
  #  assert length == len(self)
  #  return offset,length

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
##  OFPT_BARRIER_REQUEST
# C->S
# ----------------------------------------------------------------------
@openflow_c_message("OFPT_BARRIER_REQUEST", 20, request_for="ofp_barrier_reply")
class ofp_barrier_request (ofp_header):
  """
    Barrier request message

    The controller sends this message to ensure message dependencies have
    been met or receive notifications for completed operations.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  #def unpack (self, raw, offset=0):
  #  offset,length = self._unpack_header(raw, offset)
  #  assert length == len(self)
  #  return offset,length

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## Role request message
# C->S
# ----------------------------------------------------------------------  
# TODO compose into of_04.py and test
# ---------------------------------------------------------------------- 
@openflow_c_message("OFPT_ROLE_REQUEST", 24, request_for="ofp_role_reply")
class ofp_role_request (ofp_header):
  """
    When the controller wants to change its role.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    self.role = 0
    self.generation_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!L4xQ",
                          self.role,
                          self.generation_id)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)

    offset,(self.role,
            self.generation_id) = _unpack("!L4xQ", raw, offset)

    assert length == len(self)
    return offset, length

  @staticmethod
  def __len__ ():
    return len(ofp_header) + 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.role != other.role: return False
    if self.generation_id != other.generation_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'role: ' + ofp_controller_role_map.get(self.role, str(self.role)) + '\n'
    outstr += prefix + 'generation id: ' + self.generation_id + '\n'
    return outstr

# ----------------------------------------------------------------------
## Role reply message
# S->C
# ----------------------------------------------------------------------  
# TODO compose into of_04.py and test
# ---------------------------------------------------------------------- 
@openflow_s_message("OFPT_ROLE_REPLY", 25, reply_to="ofp_role_request")
class ofp_role_reply (ofp_header):
  """
    When the controller wants to change its role.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    self.role = 0
    self.generation_id = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!L4xQ",
                          self.role,
                          self.generation_id)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)

    offset,(self.role,
            self.generation_id) = _unpack("!L4xQ", raw, offset)

    assert length == len(self)
    return offset, length

  @staticmethod
  def __len__ ():
    return len(ofp_header) + 16

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.role != other.role: return False
    if self.generation_id != other.generation_id: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'role: ' + ofp_controller_role_map.get(self.role, str(self.role)) + '\n'
    outstr += prefix + 'generation id: ' + self.generation_id + '\n'
    return outstr


# ----------------------------------------------------------------------
## Get asynchronous request message - empty body
# C->S
# ----------------------------------------------------------------------  
# TODO compose into of_04.py and test
# ---------------------------------------------------------------------- 
@openflow_c_message("OFPT_GET_ASYNC_REQUEST", 26, request_for="ofp_get_async_reply")
class ofp_get_async_request (ofp_header):
  """
    When the controller wants to change its role.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return 8

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## get asynchronous reply
# S->C
# ----------------------------------------------------------------------  
# TODO compose into of_04.py and test
# TODO unpack bitmaps in show
# ---------------------------------------------------------------------- 
@openflow_s_message("OFPT_GET_ASYNC_REPLY", 27, reply_to="ofp_get_async_request")
class ofp_get_async_reply (ofp_header):
  """
    When the controller wants to change its role.
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    self.packet_in_mask_0 = 0
    self.packet_in_mask_1 = 0
    self.port_status_mask_0 = 0
    self.port_status_mask_1 = 0
    self.flow_removed_mask_0 = 0
    self.flow_removed_mask_1 = 0

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!2L2L2L",
                          self.packet_in_mask_0,
                          self.packet_in_mask_1,
                          self.port_status_mask_0,
                          self.port_status_mask_1,
                          self.flow_removed_mask_0,
                          self.flow_removed_mask_1,)
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)

    offset,(self.packet_in_mask_0,
            self.packet_in_mask_1,
            self.port_status_mask_0,
            self.port_status_mask_1,
            self.flow_removed_mask_0,
            self.flow_removed_mask_1) = _unpack("!2L2L2L", raw, offset)

    assert length == len(self)
    return offset, length

  @staticmethod
  def __len__ ():
    return len(ofp_header) + 24

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.packet_in_mask_0 != other.packet_in_mask_0: return False
    if self.packet_in_mask_1 != other.packet_in_mask_1: return False
    if self.port_status_mask_0 != other.port_status_mask_0: return False
    if self.port_status_mask_1 != other.port_status_mask_1: return False
    if self.flow_removed_mask_0 != other.flow_removed_mask_0: return False
    if self.flow_removed_mask_1 != other.flow_removed_mask_1: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'packet_in_mask_0: ' + str(self.packet_in_mask_0) + '\n'
    outstr += prefix + 'packet_in_mask_1: ' + str(self.packet_in_mask_1) + '\n'
    outstr += prefix + 'port_status_mask_0: ' + str(self.port_status_mask_0) + '\n'
    outstr += prefix + 'port_status_mask_1: ' + str(self.port_status_mask_1) + '\n'
    outstr += prefix + 'flow_removed_mask_0: ' + str(self.flow_removed_mask_0) + '\n'
    outstr += prefix + 'flow_removed_mask_1: ' + str(self.flow_removed_mask_1) + '\n'
    return outstr

# ----------------------------------------------------------------------
## set asynchronous 
# C->S
# ----------------------------------------------------------------------  
# TODO compose into of_04.py and test
# ---------------------------------------------------------------------- 
@openflow_s_message("OFPT_SET_ASYNC_REPLY", 28)
class ofp_set_async (ofp_get_async_reply):
    pass

# ----------------------------------------------------------------------
# Asynchronous Messages
# ----------------------------------------------------------------------
## OFPT_PACKET_IN
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_PACKET_IN", 10)
class ofp_packet_in (ofp_header):
  """
    Packet-In message

    The switch sends the packet that received to the controller by this
    message.

    ============= =========================================================
    Attribute     Description
    ============= =========================================================
    buffer_id     ID assigned by datapath
    total_len     Full length of frame
    reason        Reason packet is being sent.
                  OFPR_NO_MATCH
                  OFPR_ACTION
                  OFPR_INVALID_TTL
    table_id      ID of the table that was looked up
    cookie        Cookie of the flow entry that was looked up
    match         Instance of ``ofp_match``
    data          Ethernet frame
    ============= =========================================================
    """
  _MIN_LENGTH = 32
  def __init__ (self, **kw):
    ofp_header.__init__(self)

    self.in_port = None
    self._buffer_id = NO_BUFFER
    self.reason = 0
    self.table_id = 0
    self.cookie = 0
    self.match = None
    self.data = None
    self._total_len = None

    if 'total_len' in kw:
      self._total_len = kw.pop('total_len')

    initHelper(self, kw)

  def _validate (self):
    if self.data and (self.total_len < len(self.data)):
      return "total len less than data len"

  @property
  def total_len (self):
    if self._total_len is None:
      return len(self.data) if self.data else 0
    return self._total_len

  @total_len.setter
  def total_len (self, value):
    self._total_len = value

  @property
  def buffer_id (self):
    if self._buffer_id == NO_BUFFER: return None
    return self._buffer_id
  @buffer_id.setter
  def buffer_id (self, val):
    if val is None: val = NO_BUFFER
    self._buffer_id = val

  @property
  def data (self):
    return self._data
  @data.setter
  def data (self, data):
    assert assert_type("data", data, (packet_base, str))
    if data is None:
      self._data = ''
    elif isinstance(data, packet_base):
      self._data = data.pack()
    else:
      self._data = data
  
  # OFPT_PACKET_IN packing method
  def pack (self):
    # probably not necessary

    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!IHBBQ", 
                          self._buffer_id, 
                          self._total_len,
                          self.reason, 
                          self.table_id,
                          self.cookie
                         )
    packed += match.pack(self)
    packed += struct.pack("!2x")
    packed += self.data
    #TODO: Padding?  See __len__
    return packed

  @property
  def is_complete (self):
    if self.buffer_id is not None: return True
    return len(self.data) == self.total_len

  # OFPT_PACKET_IN unpacking method 
  def unpack (self, raw, offset=0):
    # probably the most important function of packet in

    if not self.match:
        self.match = ofp_match()

    offset,length = self._unpack_header(raw, offset)   


    offset,(self._buffer_id, 
            self._total_len, 
            self.reason, 
            self.table_id,
            self.cookie) = _unpack("!IHBBQ", raw, offset)

    matchlength = length - 26 - self.total_len - 4             # TODO - check 30

    #log.debug("packet in - offset after header unpack %d", offset)

    offset = self.match.unpack(raw, 
                               offset-4, 
                               flow_mod=False, 
                               match_len=matchlength) # TODO correct offset ?

    #log.debug("packet in - offset after match unpack %d", offset)
    
    if self.match._in_port:
      self.in_port = self.match._in_port

    offset += 2 # padding
    
    dataLen = length-16-(len(self.match)+4)-2
    datastart = length - self.total_len

    self.data = raw[datastart:]
    offset += self.total_len

    offset += 4 # TODO check

    #log.debug("packet in - offset after data unpack %d", offset)

    #log.debug(self.show())

    #offset = length    # bug or feature? 

    if length != len(self):
      log.debug("length %d len(self) %d matchlen %d datalen %d datastart %d", length, len(self), matchlength, dataLen, datastart)
      log.debug(self.show())

    assert length == len(self)
    return offset, length

  def __len__ (self):
    # TODO check
    return len(ofp_header) + 16 + len(self.match) + 2 + self.total_len

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.buffer_id != other.buffer_id: return False
    if self.total_len != other.total_len: return False
    if self.in_port != other.in_port: return False
    if self.reason != other.reason: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = '\n'
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'length: ' + str(len(self)) + "(hdr " + str(len(ofp_header)) + " + 16 + match " + str(len(self.match)) + " + 2 + packet " + str(self.total_len) + ')\n'
    outstr += prefix + 'buffer_id: ' + str(self.buffer_id) + '\n'
    outstr += prefix + 'total_len: ' + str(self._total_len) + '\n'
    outstr += prefix + 'in_port: ' + str(self.in_port) + '\n'
    outstr += prefix + 'reason: ' + ofp_packet_in_reason_map.get(self.reason,str(self.reason)) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'cookie: ' + str(self.cookie) + '\n'
    outstr += prefix + 'match: \n'
    outstr += ofp_match.show(self.match, prefix + '  ')
    outstr += prefix + 'data length: ' + str(len(self.data)) + '\n'
    #outstr += prefix + 'data: ' + str(self.data) + '\n'
    return outstr

# ----------------------------------------------------------------------
## Flow removed message
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_FLOW_REMOVED", 11)
class ofp_flow_removed (ofp_header):
  """
    Flow removed message

    When flow entries time out or are deleted, the switch notifies controller
    with this message.

    ================ ======================================================
    Attribute        Description
    ================ ======================================================
    cookie           Opaque controller-issued identifier
    priority         Priority level of flow entry
    reason           One of the following values.
                     OFPRR_IDLE_TIMEOUT
                     OFPRR_HARD_TIMEOUT
                     OFPRR_DELETE
                     OFPRR_GROUP_DELETE
    table_id         ID of the table
    duration_sec     Time flow was alive in seconds
    duration_nsec    Time flow was alive in nanoseconds beyond duration_sec
    idle_timeout     Idle timeout from original flow mod
    hard_timeout     Hard timeout from original flow mod
    packet_count     Number of packets that was associated with the flow
    byte_count       Number of bytes that was associated with the flow
    match            Instance of ``ofp_match``
    ================ ======================================================
  """
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.cookie = 0
    self.priority = 0
    self.reason = 0
    self.table_id = 0
    self.duration_sec = 0
    self.duration_nsec = 0
    self.idle_timeout = 0
    self.hard_timeout = 0
    self.packet_count = 0
    self.byte_count = 0
    self.match = ofp_match()
    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.match, ofp_match):
      return "match is not class ofp_match"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)

    packed += struct.pack("!QHBBLLHHQQ", 
                          self.cookie, 
                          self.priority, 
                          self.reason,
                          self.table_id,
                          self.duration_sec, 
                          self.duration_nsec,
                          self.idle_timeout,
                          self.hard_timeout,
                          self.packet_count, 
                          self.byte_count,
                         )
    packed += self.match.pack()
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.cookie, 
            self.priority, 
            self.reason,
            self.table_id,
            self.duration_sec, 
            self.duration_nsec, 
            self.idle_timeout,
            self.hard_timeout,
            self.packet_count, 
            self.byte_count) = _unpack("!QHBBLLHHQQ", raw, offset)

    offset = self.match.unpack(raw, offset)
    assert length == len(self)
    return offset,length

    log.debug(self.show())

  @staticmethod
  def __len__ ():
    return 48 + len(ofp_match)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.match != other.match: return False
    if self.cookie != other.cookie: return False
    if self.priority != other.priority: return False
    if self.reason != other.reason: return False
    if self.duration_sec != other.duration_sec: return False
    if self.duration_nsec != other.duration_nsec: return False
    if self.idle_timeout != other.idle_timeout: return False
    if self.packet_count != other.packet_count: return False
    if self.byte_count != other.byte_count: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'cookie: ' + str(self.cookie) + '\n'
    outstr += prefix + 'priority: ' + str(self.priority) + '\n'
    outstr += prefix + 'reason: ' + ofp_flow_removed_reason_map.get(self.reason,str(self.reason)) + '\n'
    outstr += prefix + 'table_id: ' + str(self.table_id) + '\n'
    outstr += prefix + 'duration_sec: ' + str(self.duration_sec) + '\n'
    outstr += prefix + 'duration_nsec: ' + str(self.duration_nsec) + '\n'
    outstr += prefix + 'idle_timeout: ' + str(self.idle_timeout) + '\n'
    outstr += prefix + 'hard_timeout: ' + str(self.hard_timeout) + '\n'
    outstr += prefix + 'packet_count: ' + str(self.packet_count) + '\n'
    outstr += prefix + 'byte_count: ' + str(self.byte_count) + '\n'
    outstr += prefix + 'match: \n'
    outstr += self.match.show(prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## port status message
# S->C
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_PORT_STATUS", 12)
class ofp_port_status (ofp_header):
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.reason = 0
    self.desc = ofp_port()

    initHelper(self, kw)

  def _validate (self):
    if not isinstance(self.desc, ofp_port):
      return "desc is not class ofp_port"
    return None

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!B7x", self.reason)
    packed += self.desc.pack()
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,(self.reason,) = _unpack("!B", raw, offset)
    offset = _skip(raw, offset, 7)
    offset = ofp_port.unpack(self.desc,raw, offset)
    
    #log.debug(self.show())

    assert length == len(self)
    return offset,length

  @staticmethod
  def __len__ ():
    return len(ofp_header) + 8 + len(ofp_port)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.reason != other.reason: return False
    if self.desc != other.desc: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'Header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'Reason: ' + ofp_port_reason_map.get(self.reason, str(self.reason)) + '\n'
    outstr += prefix + 'Port description: \n'
    outstr += self.desc.show(prefix + '  ')
    return outstr

# ----------------------------------------------------------------------
## ofp error message
# S->C
# ----------------------------------------------------------------------
# TODO add group/table/meter/role/async errors
# ----------------------------------------------------------------------
@openflow_s_message("OFPT_ERROR", 1)
class ofp_error (ofp_header):
  _MIN_LENGTH = 12
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.type = 0
    self.code = 0
    self.data = b''

    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!HH", self.type, self.code)
    packed += self.data
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)

    offset,(self.type, self.code) = _unpack("!HH", raw, offset)

    self.data = raw[offset:length]
    offset = length

    assert length == len(self)
    return offset,length

  def __len__ (self):
    return 12 + len(self.data)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.type != other.type: return False
    if self.code != other.code: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    t = self.type
    c = self.code
    if t < len(ofp_error_type):
      n = ofp_error_type_map[t]
      t = "%s (%i)" % (n, t)
      n = 'ofp' + n.lower()[5:] + '_code_map'
      if n in sys.modules[__name__].__dict__:
        if c in sys.modules[__name__].__dict__[n]:
          c = "%s (%i)" % (sys.modules[__name__].__dict__[n][c], c)
    outstr += prefix + 'type: ' + str(t) + '\n'
    outstr += prefix + 'code: ' + str(c) + '\n'
    if len(self.data):
      outstr += prefix + 'datalen: %s\n' % (len(self.data),)
      outstr += prefix + hexdump(self.data).replace("\n", "\n" + prefix)
    return outstr.strip()

# ----------------------------------------------------------------------
# Symmetric Messages
# ----------------------------------------------------------------------
## initial hello message
# C<->S
# ----------------------------------------------------------------------
@openflow_sc_message("OFPT_HELLO", 0)
class ofp_hello (ofp_header):
  def __init__ (self, **kw):
    self.length = 8
    self.elements = []

    ofp_header.__init__(self)
    initHelper(self, kw)
  
  # packing without elements
  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    return packed

  # unpacking with elements 
  def unpack (self, raw, offset=0):
    offset_target = offset
    offset, self.length = self._unpack_header(raw, offset)
   
    offset_target += self.length
    #log.debug ("hello (beginning) offset %d self.length %d offset target %d", offset, self.length, offset_target)
    
    # unpacking of elements
    
    while offset < offset_target:
      element = ofp_hello_elem_header()
      offset = ofp_hello_elem_header.unpack(element, raw, offset)

      #log.debug(element.show())
      #log.debug("hello offset after element %d",offset)

    #log.debug ("hello (end) offset %d self.length %d offset target %d", offset, self.length, offset_target)
    assert self.length == len(self)
    return offset, self.length

  def __len__ (self):
    return self.length

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    # TODO elements
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')

    # todo elements

    return outstr

# ----------------------------------------------------------------------
## echo request message
# ----------------------------------------------------------------------
@openflow_sc_message("OFPT_ECHO_REQUEST", 2,
    request_for="ofp_echo_reply")
class ofp_echo_request (ofp_header):
  """
    An Echo Request message consists of an OpenFlow header plus an arbitrary-length data field. The
    data field might be a message timestamp to check latency, various lengths to measure bandwidth, or
    zero-size to verify liveness between the switch and controller.
  """
  _MIN_LENGTH = 8

  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.body = b''
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += self.body
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    
    

    if length is None:
      offset,self.body = _read(raw, offset, length - 8)
      log.debug('No data field')

    assert length == len(self)
    return offset,length


  def __len__ (self):
    return 8 + len(self.body)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.body != other.body: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'body:\n'
    outstr += _format_body(self.body, prefix + '  ') + '\n'
    return outstr

# ----------------------------------------------------------------------
## echo reply message
# ----------------------------------------------------------------------
@openflow_sc_message("OFPT_ECHO_REPLY", 3,
    reply_to="ofp_echo_request")
class ofp_echo_reply (ofp_header):
  """
    An Echo Reply message consists of an OpenFlow header plus the unmodi
ed data 
eld of an echo
    request message.
  """
  _MIN_LENGTH = 8
  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.body = b''
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += self.body
    return packed

  def unpack (self, raw, offset=0):
    offset,length = self._unpack_header(raw, offset)
    offset,self.body = _read(raw, offset, length - 8)
    assert length == len(self)
    return offset,length

  def __len__ (self):
    return 8 + len(self.body)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.body != other.body: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'body:\n'
    outstr += _format_body(self.body, prefix + '  ') + '\n'
    return outstr


# ----------------------------------------------------------------------
##  Experimenter extension message
# ----------------------------------------------------------------------
# Base class for experimenter messages
class ofp_experimenter_base (ofp_header):
  header_type = 4   # OFPT_EXPERIMENTER
  pass

@openflow_sc_message("OFPT_EXPERIMENTER", 4)
class ofp_experimenter_generic (ofp_experimenter_base):
  _MIN_LENGTH = 16
  _collect_raw = False

  def __init__ (self, **kw):
    ofp_header.__init__(self)
    self.experimenter = 0
    self.exp_type = 0

    self.data = b''
    initHelper(self, kw)

  def pack (self):
    assert self._assert()

    packed = b""
    packed += ofp_header.pack(self)
    packed += struct.pack("!LL", 
                          self.experimenter, 
                          self.exp_type)
    if hasattr(self.data, "pack"):
      packed += self.data.pack()
    else:
      packed += self.data
    return packed

  def unpack (self, raw, offset=0):
    _offset = offset
    offset,length = self._unpack_header(raw, offset)
    offset,(self.experimenter,
            self.exp_type) = _unpack("!LL", raw, offset)
    offset,self.data = _read(raw, offset, length-16)
    if self._collect_raw:
      self.raw = raw[_offset, _offset+length]
    return offset,length

  def __len__ (self):
    return 16 + len(self.data)

  def __eq__ (self, other):
    if type(self) != type(other): return False
    if not ofp_header.__eq__(self, other): return False
    if self.experimenter != other.experimenter: return False
    if self.data != other.data: return False
    return True

  def show (self, prefix=''):
    outstr = ''
    outstr += prefix + 'header: \n'
    outstr += ofp_header.show(self, prefix + '  ')
    outstr += prefix + 'experimenter: ' + str(self.experimenter) + '\n'
    outstr += prefix + 'exp_type: ' + str(self.exp_type) + '\n'
    outstr += prefix + 'datalen: ' + str(len(self.data)) + '\n'
    #outstr += prefix + hexdump(self.data).replace("\n", "\n" + prefix)
    return outstr


# ----------------------------------------------------------------------
# well .. aren't these unpackers a bit lost?
# ----------------------------------------------------------------------
def _unpack_queue_props (b, length, offset=0):
  """
  Parses queue props from a buffer
  b is a buffer (bytes)
  offset, if specified, is where in b to start decoding
  returns (next_offset, [Pops])
  """
  if (len(b) - offset) < length: raise UnderrunError
  props = []
  end = length + offset
  while offset < end:
    (t,l) = struct.unpack_from("!HH", b, offset)
    if (len(b) - offset) < l: raise UnderrunError
    a = _queue_prop_type_to_class.get(t)
    if a is None:
      # Use generic prop header for unknown type
      a = ofp_queue_prop_generic()
    else:
      a = a()
    a.unpack(b[offset:offset+l])
    assert len(a) == l
    props.append(a)
    offset += l
  return (offset, props)

# ----------------------------------------------------------------------
def _unpack_actions (b, length, offset=0):
  """
  Parses actions from a buffer
  b is a buffer (bytes)
  offset, if specified, is where in b to start decoding
  returns (next_offset, [Actions])
  """
  if (len(b) - offset) < length: raise UnderrunError
  actions = []
  end = length + offset
  while offset < end:
    (t,l) = struct.unpack_from("!HH", b, offset)
    if (len(b) - offset) < l: raise UnderrunError
    a = _action_type_to_class.get(t)
    if a is None:
      # Use generic action header for unknown type
      a = ofp_action_generic()
    else:
      a = a()
    a.unpack(b[offset:offset+l])
    assert len(a) == l
    actions.append(a)
    offset += l
  return (offset, actions)

def _init ():
  def formatMap (name, m):
    o = name + " = {\n"
    vk = sorted([(v,k) for k,v in m.iteritems()])
    maxlen = 2 + len(reduce(lambda a,b: a if len(a)>len(b) else b,
                            (v for k,v in vk)))
    fstr = "  %-" + str(maxlen) + "s : %s,\n"
    for v,k in vk:
      o += fstr % ("'" + k + "'",v)
    o += "}"
    return o
  """
  maps = []
  for k,v in globals().iteritems():
    if k.startswith("ofp_") and k.endswith("_map") and type(v) == dict:
      maps.append((k,v))
  for name,m in maps:
    rev = {}
    name = name[:-4]
    names = globals()[name]
    for n in names:
      rev[n] = globals()[n]

    globals()[name + '_rev_map'] = rev
    print(formatMap(name + "_rev_map", rev))
  return
  """
  maps = []
  for k,v in globals().iteritems():
    if (k.startswith("ofp_") and k.endswith("_rev_map")
        and type(v) == dict):
      maps.append((k[:-8],v))
  for name,m in maps:
    # Try to generate forward maps
    forward = dict(((v,k) for k,v in m.iteritems()))
    if len(forward) == len(m):
      if name + "_map" not in globals():
        globals()[name + "_map"] = forward
    else:
      print(name + "_rev_map is not a map")

    # Try to generate lists
    v = m.values()
    v.sort()
    if v[-1] != len(v)-1:
      # Allow ones where the last value is a special value (e.g., experimenter)
      del v[-1]
    if len(v) > 0 and v[0] == 0 and v[-1] == len(v)-1:
      globals()[name] = v

    # Generate gobals
    for k,v in m.iteritems():
      globals()[k] = v


_init()
