#!/usr/bin/python
# -*- coding: utf-8 -*-

#  Copyright 2015 Alexander Craig
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
Module implementing fixed length bloom filters, elias-gamma encoding, and packing of bloom 
filters into the BloomFlow shim header format, which is structured as follows:

| E-G Encoded Bloom Filter Length | E-G Encoded Number of Hash Functions | Bloom Filter Bit Array |

All bit arrays are stored in big endian format.
"""

import sys
import pyhash
import numpy
from bitarray import bitarray
from struct import pack, unpack
import numpy as np
import math

UINT32_ROLLOVER = 2**32
murmurhash2_hasher = pyhash.murmur2_neutral_32()
lookup3_hasher = pyhash.lookup3_little()
MAX_NUM_BITS = 320

def bitarray_to_str(bit_array):
    """Returns the binary string representation of the passed bit array."""
    byte_array = bit_array.tobytes()
    return_str = ''
    for i in range(0, len(byte_array)):
        return_str += '{0:08b}'.format(ord(byte_array[i]))
    return return_str

def encode_elias_gamma(value):
    """Encodes a value into Elias-Gamma format, and returns the bit array representation."""
    eg_num_leading_zeros = int(math.floor(np.log2(value)))
    eg_num_bits = (2 * eg_num_leading_zeros) + 1
    eg_bit_array = bitarray(eg_num_bits, endian='big')
    eg_bit_array.setall(False)
    eg_bit_array[eg_num_leading_zeros:] = bitarray(bin(value)[2:])
    return eg_bit_array

def decode_elias_gamma(eg_bit_array):
    """Decodes an Elias-Gamma encoded value from the specified bit array.
    
    If multiple Elias-Gamma encoded values are found in the array, only the first
    is returned. A ValueError is raised if no valid Elias-Gamma encoding is found 
    (i.e. if the bit array is all zeros).
    """
    num_leading_zeros = eg_bit_array.index(True)
    return int(eg_bit_array[num_leading_zeros:].unpack(zero='0', one='1'), 2)

class bloom_filter:
    """Class representing a bloom filter with fixed bit length and a fixed number of hash functions.
    
    Hash function G_i(x) is generated via the formula:
    G_i(x) = (H_1(x) + [i * H_2(x)]) % filter_len
    
    where:
    
    x = Key to be hashed
    i = Hash function index
    H_1(x) = murmurhash2_neutral
    H_2(x) = lookup3c_little
    
    Integer values are accepted as hash keys.
    """
    
    def __init__(self, num_bits, num_hash_functions):
        """Initializes the bloom filter, allocating a bitarray with the specified number of bits."""
        self.num_bits = int(num_bits)
        self.num_hash_functions = int(num_hash_functions)
        self.filter_bits = bitarray(MAX_NUM_BITS, endian='big')
        self.filter_bits[0:self.num_bits] = 0
        self.num_hashes_last_op = 0
    
    def check_member(self, int_key):
        """Returns True if the specified integer key has been added to the hash function, or if abs
        false positive hash collision occurs.
        """
        for hash_index in range(0, self.num_hash_functions):
            if self.filter_bits[self.__generate_hashcode(int_key, hash_index)] == False:
                self.num_hashes_last_op = hash_index + 1
                return False
        
        self.num_hashes_last_op = self.num_hash_functions
        return True
    
    def add_member(self, int_key):
        """Adds the specified integer key to the bloom filter."""
        for hash_index in range(0, self.num_hash_functions):
            self.filter_bits[self.__generate_hashcode(int_key, hash_index)] = True
        
    def clear_and_resize(self, new_num_bits, num_hash_functions):
        """Clears the bloom filter, resizes it to the specified number of bits. The number of hash functions is also set to the provided value."""
        self.num_bits = int(new_num_bits)
        self.filter_bits[0:self.num_bits] = 0
        self.num_hash_functions = int(num_hash_functions)
    
    def pack_shim_header(self):
        """Returns a bitarray encoding the bloom filter in the BloomFlow shim header format."""
        shim_bit_array = encode_elias_gamma(self.num_bits)
        shim_bit_array.extend(encode_elias_gamma(self.num_hash_functions))
        shim_bit_array.extend(self.filter_bits[0:self.num_bits])
        return shim_bit_array
    
    def __generate_hashcode(self, int_key, hash_index):
        """Implements the hash code generation function: G_i(x) = (H_1(x) + [i * H_2(x)]) % filter_len."""
        key_bytes = pack('=H', int_key)
        h1_hash_val = murmurhash2_hasher(key_bytes)
        h2_hash_val = lookup3_hasher(key_bytes)
        return ((h1_hash_val + (hash_index * h2_hash_val)) % (UINT32_ROLLOVER)) % self.num_bits
    
    def debug_str(self):
        """Returns a string including the binary string representation of the hash filter (for debugging only)."""
        return_str = 'BloomFilter - NumBits: ' + str(self.num_bits) + ', NumHashFunctions: ' + str(self.num_hash_functions) + '\n'
        return_str += bitarray_to_str(self.filter_bits[0:self.num_bits])
        return return_str