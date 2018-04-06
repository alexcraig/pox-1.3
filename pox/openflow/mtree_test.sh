#!/bin/sh
#export PATH=$PATH:/home/mininet/pox-1.3;
sudo python kill_running_test.py;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT2_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=2;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT1_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=1;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT3_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=3;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT4_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=4;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT5_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=5;
sudo python bloomflow_multicast.py graphml_topo topology_path=../topologies/Ibm.graphml num_iterations=50 log_prefix=Ibm_500B_Recv3_MT6_ num_groups=1 group_mbits_per_second=1 group_packet_size_bytes=500 group_size_min=3 group_size_max=3 num_multi_trees=6;
