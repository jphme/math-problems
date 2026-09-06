import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange21
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled20Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_1000 : ProfileBox := { lower := ![(1 : ℚ) / 40, (169 : ℚ) / 256, (1 : ℚ) / 40, (999 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (107 : ℚ) / 160, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1001 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1002 : ProfileBox := branch_box_1002
def node_box_1003 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1004 : ProfileBox := branch_box_1004
def node_box_1005 : ProfileBox := branch_box_1005
def node_box_1006 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1007 : ProfileBox := branch_box_1007
def node_box_1008 : ProfileBox := { lower := ![(3 : ℚ) / 80, (169 : ℚ) / 256, (1 : ℚ) / 40, (247 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1009 : ProfileBox := branch_box_1009
def node_box_1010 : ProfileBox := { lower := ![(3 : ℚ) / 80, (169 : ℚ) / 256, (1 : ℚ) / 40, (999 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1011 : ProfileBox := { lower := ![(1 : ℚ) / 40, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1012 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1013 : ProfileBox := { lower := ![(1 : ℚ) / 40, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1014 : ProfileBox := branch_box_1014
def node_box_1015 : ProfileBox := branch_box_1015
def node_box_1016 : ProfileBox := { lower := ![(1 : ℚ) / 40, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1017 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1018 : ProfileBox := branch_box_1018
def node_box_1019 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1020 : ProfileBox := branch_box_1020
def node_box_1021 : ProfileBox := branch_box_1021
def node_box_1022 : ProfileBox := { lower := ![(3 : ℚ) / 80, (417 : ℚ) / 640, (1 : ℚ) / 40, (101 : ℚ) / 128, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (3 : ℚ) / 80, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1023 : ProfileBox := { lower := ![(1 : ℚ) / 20, (3 : ℚ) / 5, (0 : ℚ) / 1, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_1024 : ProfileBox := branch_box_1024
def node_box_1025 : ProfileBox := { lower := ![(1 : ℚ) / 20, (3 : ℚ) / 5, (0 : ℚ) / 1, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_1026 : ProfileBox := branch_box_1026
def node_box_1027 : ProfileBox := { lower := ![(1 : ℚ) / 20, (3 : ℚ) / 5, (0 : ℚ) / 1, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1028 : ProfileBox := branch_box_1028
def node_box_1029 : ProfileBox := branch_box_1029
def node_box_1030 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1031 : ProfileBox := branch_box_1031
def node_box_1032 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1033 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1034 : ProfileBox := { lower := ![(3 : ℚ) / 40, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (107 : ℚ) / 160, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1035 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1036 : ProfileBox := branch_box_1036
def node_box_1037 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1038 : ProfileBox := branch_box_1038
def node_box_1039 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1040 : ProfileBox := branch_box_1040
def node_box_1041 : ProfileBox := branch_box_1041
def node_box_1042 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1043 : ProfileBox := branch_box_1043
def node_box_1044 : ProfileBox := { lower := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1045 : ProfileBox := branch_box_1045
def node_box_1046 : ProfileBox := { lower := ![(1 : ℚ) / 20, (417 : ℚ) / 640, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1047 : ProfileBox := { lower := ![(1 : ℚ) / 20, (417 : ℚ) / 640, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1048 : ProfileBox := { lower := ![(1 : ℚ) / 20, (417 : ℚ) / 640, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 40, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1049 : ProfileBox := { lower := ![(1 : ℚ) / 20, (417 : ℚ) / 640, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 16, (107 : ℚ) / 160, (1 : ℚ) / 40, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }

def split_1001_accepted : Bool := splitNodeOK node_box_1001 node_box_1003 node_box_1004 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_1003_accepted : Bool := splitNodeOK node_box_1003 node_box_1005 node_box_1006 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_1006_accepted : Bool := splitNodeOK node_box_1006 node_box_1007 node_box_1008 ⟨1, by omega⟩ ((169 : ℚ) / 256)
def split_1008_accepted : Bool := splitNodeOK node_box_1008 node_box_1009 node_box_1010 ⟨3, by omega⟩ ((999 : ℚ) / 1280)
def split_1011_accepted : Bool := splitNodeOK node_box_1011 node_box_1013 node_box_1014 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_1012_accepted : Bool := splitNodeOK node_box_1012 node_box_1017 node_box_1018 ⟨2, by omega⟩ ((3 : ℚ) / 80)
def split_1013_accepted : Bool := splitNodeOK node_box_1013 node_box_1015 node_box_1016 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_1017_accepted : Bool := splitNodeOK node_box_1017 node_box_1019 node_box_1020 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_1019_accepted : Bool := splitNodeOK node_box_1019 node_box_1021 node_box_1022 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_1023_accepted : Bool := splitNodeOK node_box_1023 node_box_1025 node_box_1026 ⟨5, by omega⟩ ((1 : ℚ) / 20)
def split_1025_accepted : Bool := splitNodeOK node_box_1025 node_box_1027 node_box_1028 ⟨7, by omega⟩ ((1 : ℚ) / 20)
def split_1027_accepted : Bool := splitNodeOK node_box_1027 node_box_1029 node_box_1030 ⟨1, by omega⟩ ((203 : ℚ) / 320)
def split_1030_accepted : Bool := splitNodeOK node_box_1030 node_box_1031 node_box_1032 ⟨3, by omega⟩ ((247 : ℚ) / 320)
def split_1032_accepted : Bool := splitNodeOK node_box_1032 node_box_1033 node_box_1034 ⟨0, by omega⟩ ((3 : ℚ) / 40)
def split_1033_accepted : Bool := splitNodeOK node_box_1033 node_box_1035 node_box_1036 ⟨2, by omega⟩ ((1 : ℚ) / 40)
def split_1034_accepted : Bool := splitNodeOK node_box_1034 node_box_1081 node_box_1082 ⟨2, by omega⟩ ((1 : ℚ) / 40)
def split_1035_accepted : Bool := splitNodeOK node_box_1035 node_box_1037 node_box_1038 ⟨5, by omega⟩ ((1 : ℚ) / 40)
def split_1037_accepted : Bool := splitNodeOK node_box_1037 node_box_1039 node_box_1040 ⟨7, by omega⟩ ((1 : ℚ) / 40)
def split_1039_accepted : Bool := splitNodeOK node_box_1039 node_box_1041 node_box_1042 ⟨4, by omega⟩ ((39 : ℚ) / 40)
def split_1042_accepted : Bool := splitNodeOK node_box_1042 node_box_1043 node_box_1044 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_1044_accepted : Bool := splitNodeOK node_box_1044 node_box_1045 node_box_1046 ⟨1, by omega⟩ ((417 : ℚ) / 640)
def split_1046_accepted : Bool := splitNodeOK node_box_1046 node_box_1047 node_box_1048 ⟨3, by omega⟩ ((101 : ℚ) / 128)
def split_1047_accepted : Bool := splitNodeOK node_box_1047 node_box_1049 node_box_1050 ⟨0, by omega⟩ ((1 : ℚ) / 16)
def split_1048_accepted : Bool := splitNodeOK node_box_1048 node_box_1069 node_box_1070 ⟨0, by omega⟩ ((1 : ℚ) / 16)
def split_1049_accepted : Bool := splitNodeOK node_box_1049 node_box_1051 node_box_1052 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_batch_20_values : List Bool := [split_1001_accepted, split_1003_accepted, split_1006_accepted, split_1008_accepted, split_1011_accepted, split_1012_accepted, split_1013_accepted, split_1017_accepted, split_1019_accepted, split_1023_accepted, split_1025_accepted, split_1027_accepted, split_1030_accepted, split_1032_accepted, split_1033_accepted, split_1034_accepted, split_1035_accepted, split_1037_accepted, split_1039_accepted, split_1042_accepted, split_1044_accepted, split_1046_accepted, split_1047_accepted, split_1048_accepted, split_1049_accepted]
theorem split_batch_20_ok : split_batch_20_values.all id = true := by
  native_decide

def terminal_1000_accepted : Bool := LeafChecks.checkCore node_box_1000
def terminal_1010_accepted : Bool := LeafChecks.checkCore node_box_1010
def terminal_1016_accepted : Bool := LeafChecks.checkCore node_box_1016
def terminal_1022_accepted : Bool := LeafChecks.checkCore node_box_1022
def terminal_batch_20_values : List Bool := [terminal_1000_accepted, terminal_1010_accepted, terminal_1016_accepted, terminal_1022_accepted]
theorem terminal_batch_20_ok : terminal_batch_20_values.all id = true := by
  native_decide

theorem split_1049_ok : split_1049_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1049_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1049 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1049) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1049 node_box_1051 node_box_1052 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1049_accepted] using split_1049_ok) tree_1051 tree_1052

theorem split_1048_ok : split_1048_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1048_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1048 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1048) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1048 node_box_1069 node_box_1070 ⟨0, by omega⟩ ((1 : ℚ) / 16)
    (by simpa [split_1048_accepted] using split_1048_ok) tree_1069 tree_1070

theorem split_1047_ok : split_1047_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1047_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1047 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1047) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1047 node_box_1049 node_box_1050 ⟨0, by omega⟩ ((1 : ℚ) / 16)
    (by simpa [split_1047_accepted] using split_1047_ok) tree_1049 tree_1050

theorem split_1046_ok : split_1046_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1046_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1046 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1046) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1046 node_box_1047 node_box_1048 ⟨3, by omega⟩ ((101 : ℚ) / 128)
    (by simpa [split_1046_accepted] using split_1046_ok) tree_1047 tree_1048

theorem tree_1045 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1045) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1045] using leaf_1045_BranchSafe))⟩

theorem split_1044_ok : split_1044_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1044_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1044 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1044) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1044 node_box_1045 node_box_1046 ⟨1, by omega⟩ ((417 : ℚ) / 640)
    (by simpa [split_1044_accepted] using split_1044_ok) tree_1045 tree_1046

theorem tree_1043 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1043) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1043] using leaf_1043_BranchSafe))⟩

theorem split_1042_ok : split_1042_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1042_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1042 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1042) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1042 node_box_1043 node_box_1044 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_1042_accepted] using split_1042_ok) tree_1043 tree_1044

theorem tree_1041 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1041) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1041] using leaf_1041_BranchSafe))⟩

theorem tree_1040 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1040) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1040] using leaf_1040_BranchSafe))⟩

theorem split_1039_ok : split_1039_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1039_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1039 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1039) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1039 node_box_1041 node_box_1042 ⟨4, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_1039_accepted] using split_1039_ok) tree_1041 tree_1042

theorem tree_1038 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1038) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1038] using leaf_1038_BranchSafe))⟩

theorem split_1037_ok : split_1037_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1037_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1037 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1037) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1037 node_box_1039 node_box_1040 ⟨7, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1037_accepted] using split_1037_ok) tree_1039 tree_1040

theorem tree_1036 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1036) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1036] using leaf_1036_BranchSafe))⟩

theorem split_1035_ok : split_1035_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1035_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1035 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1035) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1035 node_box_1037 node_box_1038 ⟨5, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1035_accepted] using split_1035_ok) tree_1037 tree_1038

theorem split_1034_ok : split_1034_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1034_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1034 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1034) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1034 node_box_1081 node_box_1082 ⟨2, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1034_accepted] using split_1034_ok) tree_1081 tree_1082

theorem split_1033_ok : split_1033_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1033_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1033 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1033) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1033 node_box_1035 node_box_1036 ⟨2, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1033_accepted] using split_1033_ok) tree_1035 tree_1036

theorem split_1032_ok : split_1032_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1032_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1032 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1032) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1032 node_box_1033 node_box_1034 ⟨0, by omega⟩ ((3 : ℚ) / 40)
    (by simpa [split_1032_accepted] using split_1032_ok) tree_1033 tree_1034

theorem tree_1031 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1031) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1031] using leaf_1031_BranchSafe))⟩

theorem split_1030_ok : split_1030_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1030_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1030 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1030) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1030 node_box_1031 node_box_1032 ⟨3, by omega⟩ ((247 : ℚ) / 320)
    (by simpa [split_1030_accepted] using split_1030_ok) tree_1031 tree_1032

theorem tree_1029 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1029) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1029] using leaf_1029_BranchSafe))⟩

theorem tree_1028 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1028) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1028] using leaf_1028_BranchSafe))⟩

theorem split_1027_ok : split_1027_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1027_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1027 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1027) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1027 node_box_1029 node_box_1030 ⟨1, by omega⟩ ((203 : ℚ) / 320)
    (by simpa [split_1027_accepted] using split_1027_ok) tree_1029 tree_1030

theorem tree_1026 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1026) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1026] using leaf_1026_BranchSafe))⟩

theorem split_1025_ok : split_1025_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1025_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1025 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1025) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1025 node_box_1027 node_box_1028 ⟨7, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_1025_accepted] using split_1025_ok) tree_1027 tree_1028

theorem tree_1024 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1024) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1024] using leaf_1024_BranchSafe))⟩

theorem split_1023_ok : split_1023_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1023_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1023 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1023) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1023 node_box_1025 node_box_1026 ⟨5, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_1023_accepted] using split_1023_ok) tree_1025 tree_1026

theorem terminal_1022_ok : terminal_1022_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_20_ok terminal_1022_accepted
    (by simp [terminal_batch_20_values])
  exact h
theorem tree_1022 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1022) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1022
  simpa [terminal_1022_accepted] using terminal_1022_ok

theorem tree_1021 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1021) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1021] using leaf_1021_BranchSafe))⟩

theorem tree_1020 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1020) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1020] using leaf_1020_BranchSafe))⟩

theorem split_1019_ok : split_1019_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1019_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1019 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1019) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1019 node_box_1021 node_box_1022 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_1019_accepted] using split_1019_ok) tree_1021 tree_1022

theorem tree_1018 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1018) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1018] using leaf_1018_BranchSafe))⟩

theorem split_1017_ok : split_1017_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1017_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1017 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1017) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1017 node_box_1019 node_box_1020 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1017_accepted] using split_1017_ok) tree_1019 tree_1020

theorem terminal_1016_ok : terminal_1016_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_20_ok terminal_1016_accepted
    (by simp [terminal_batch_20_values])
  exact h
theorem tree_1016 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1016) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1016
  simpa [terminal_1016_accepted] using terminal_1016_ok

theorem tree_1015 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1015) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1015] using leaf_1015_BranchSafe))⟩

theorem tree_1014 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1014) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1014] using leaf_1014_BranchSafe))⟩

theorem split_1013_ok : split_1013_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1013_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1013 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1013) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1013 node_box_1015 node_box_1016 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_1013_accepted] using split_1013_ok) tree_1015 tree_1016

theorem split_1012_ok : split_1012_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1012_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1012 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1012) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1012 node_box_1017 node_box_1018 ⟨2, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_1012_accepted] using split_1012_ok) tree_1017 tree_1018

theorem split_1011_ok : split_1011_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1011_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1011 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1011) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1011 node_box_1013 node_box_1014 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1011_accepted] using split_1011_ok) tree_1013 tree_1014

theorem terminal_1010_ok : terminal_1010_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_20_ok terminal_1010_accepted
    (by simp [terminal_batch_20_values])
  exact h
theorem tree_1010 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1010) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1010
  simpa [terminal_1010_accepted] using terminal_1010_ok

theorem tree_1009 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1009) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1009] using leaf_1009_BranchSafe))⟩

theorem split_1008_ok : split_1008_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1008_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1008 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1008) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1008 node_box_1009 node_box_1010 ⟨3, by omega⟩ ((999 : ℚ) / 1280)
    (by simpa [split_1008_accepted] using split_1008_ok) tree_1009 tree_1010

theorem tree_1007 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1007) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1007] using leaf_1007_BranchSafe))⟩

theorem split_1006_ok : split_1006_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1006_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1006 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1006) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1006 node_box_1007 node_box_1008 ⟨1, by omega⟩ ((169 : ℚ) / 256)
    (by simpa [split_1006_accepted] using split_1006_ok) tree_1007 tree_1008

theorem tree_1005 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1005) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1005] using leaf_1005_BranchSafe))⟩

theorem tree_1004 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1004) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1004] using leaf_1004_BranchSafe))⟩

theorem split_1003_ok : split_1003_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1003_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1003 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1003) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1003 node_box_1005 node_box_1006 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_1003_accepted] using split_1003_ok) tree_1005 tree_1006

theorem tree_1002 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1002) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1002] using leaf_1002_BranchSafe))⟩

theorem split_1001_ok : split_1001_accepted = true := by
  have h := List.all_eq_true.mp split_batch_20_ok split_1001_accepted
    (by simp [split_batch_20_values])
  exact h
theorem tree_1001 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1001) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1001 node_box_1003 node_box_1004 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1001_accepted] using split_1001_ok) tree_1003 tree_1004

theorem terminal_1000_ok : terminal_1000_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_20_ok terminal_1000_accepted
    (by simp [terminal_batch_20_values])
  exact h
theorem tree_1000 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1000) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1000
  simpa [terminal_1000_accepted] using terminal_1000_ok

#print axioms tree_1000
end PeaceableQueens.UpperBound.Generated.Even.Core
