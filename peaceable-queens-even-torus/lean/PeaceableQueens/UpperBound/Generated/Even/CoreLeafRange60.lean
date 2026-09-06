import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange61
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled60Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_3000 : ProfileBox := branch_box_3000
def node_box_3001 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (483 : ℚ) / 640, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_3002 : ProfileBox := branch_box_3002
def node_box_3003 : ProfileBox := branch_box_3003
def node_box_3004 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_3005 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (911 : ℚ) / 1280, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_3006 : ProfileBox := branch_box_3006
def node_box_3007 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (911 : ℚ) / 1280, (1 : ℚ) / 40, (977 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_3008 : ProfileBox := branch_box_3008
def node_box_3009 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3010 : ProfileBox := branch_box_3010
def node_box_3011 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3012 : ProfileBox := branch_box_3012
def node_box_3013 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3014 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3015 : ProfileBox := branch_box_3015
def node_box_3016 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3017 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3018 : ProfileBox := branch_box_3018
def node_box_3019 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (191 : ℚ) / 256, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3020 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (191 : ℚ) / 256, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3021 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (191 : ℚ) / 256, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (371 : ℚ) / 512, (1 : ℚ) / 40, (483 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3022 : ProfileBox := branch_box_3022
def node_box_3023 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3024 : ProfileBox := branch_box_3024
def node_box_3025 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (59 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (191 : ℚ) / 256, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3026 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (191 : ℚ) / 256, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (933 : ℚ) / 1280, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3027 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (0 : ℚ) / 1, (191 : ℚ) / 256, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (371 : ℚ) / 512, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3028 : ProfileBox := branch_box_3028
def node_box_3029 : ProfileBox := branch_box_3029
def node_box_3030 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (19 : ℚ) / 20, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3031 : ProfileBox := branch_box_3031
def node_box_3032 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3033 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3034 : ProfileBox := branch_box_3034
def node_box_3035 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3036 : ProfileBox := branch_box_3036
def node_box_3037 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3038 : ProfileBox := branch_box_3038
def node_box_3039 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_3040 : ProfileBox := branch_box_3040
def node_box_3041 : ProfileBox := branch_box_3041
def node_box_3042 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_3043 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (59 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 40, (483 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 160, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_3044 : ProfileBox := branch_box_3044
def node_box_3045 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 40, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_3046 : ProfileBox := branch_box_3046
def node_box_3047 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 40, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (247 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_3048 : ProfileBox := branch_box_3048
def node_box_3049 : ProfileBox := branch_box_3049

def split_3001_accepted : Bool := splitNodeOK node_box_3001 node_box_3003 node_box_3004 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_3004_accepted : Bool := splitNodeOK node_box_3004 node_box_3005 node_box_3006 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
def split_3005_accepted : Bool := splitNodeOK node_box_3005 node_box_3007 node_box_3008 ⟨3, by omega⟩ ((977 : ℚ) / 1280)
def split_3009_accepted : Bool := splitNodeOK node_box_3009 node_box_3011 node_box_3012 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_3011_accepted : Bool := splitNodeOK node_box_3011 node_box_3013 node_box_3014 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_3013_accepted : Bool := splitNodeOK node_box_3013 node_box_3015 node_box_3016 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_3014_accepted : Bool := splitNodeOK node_box_3014 node_box_3023 node_box_3024 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
def split_3016_accepted : Bool := splitNodeOK node_box_3016 node_box_3017 node_box_3018 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
def split_3017_accepted : Bool := splitNodeOK node_box_3017 node_box_3019 node_box_3020 ⟨3, by omega⟩ ((191 : ℚ) / 256)
def split_3020_accepted : Bool := splitNodeOK node_box_3020 node_box_3021 node_box_3022 ⟨1, by omega⟩ ((371 : ℚ) / 512)
def split_3023_accepted : Bool := splitNodeOK node_box_3023 node_box_3025 node_box_3026 ⟨3, by omega⟩ ((191 : ℚ) / 256)
def split_3026_accepted : Bool := splitNodeOK node_box_3026 node_box_3027 node_box_3028 ⟨1, by omega⟩ ((371 : ℚ) / 512)
def split_3030_accepted : Bool := splitNodeOK node_box_3030 node_box_3031 node_box_3032 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_3032_accepted : Bool := splitNodeOK node_box_3032 node_box_3033 node_box_3034 ⟨1, by omega⟩ ((461 : ℚ) / 640)
def split_3033_accepted : Bool := splitNodeOK node_box_3033 node_box_3035 node_box_3036 ⟨3, by omega⟩ ((483 : ℚ) / 640)
def split_3035_accepted : Bool := splitNodeOK node_box_3035 node_box_3037 node_box_3038 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_3037_accepted : Bool := splitNodeOK node_box_3037 node_box_3039 node_box_3040 ⟨7, by omega⟩ ((3 : ℚ) / 80)
def split_3039_accepted : Bool := splitNodeOK node_box_3039 node_box_3041 node_box_3042 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_3042_accepted : Bool := splitNodeOK node_box_3042 node_box_3043 node_box_3044 ⟨5, by omega⟩ ((1 : ℚ) / 160)
def split_3045_accepted : Bool := splitNodeOK node_box_3045 node_box_3047 node_box_3048 ⟨7, by omega⟩ ((1 : ℚ) / 40)
def split_3047_accepted : Bool := splitNodeOK node_box_3047 node_box_3049 node_box_3050 ⟨4, by omega⟩ ((39 : ℚ) / 40)
def split_batch_60_values : List Bool := [split_3001_accepted, split_3004_accepted, split_3005_accepted, split_3009_accepted, split_3011_accepted, split_3013_accepted, split_3014_accepted, split_3016_accepted, split_3017_accepted, split_3020_accepted, split_3023_accepted, split_3026_accepted, split_3030_accepted, split_3032_accepted, split_3033_accepted, split_3035_accepted, split_3037_accepted, split_3039_accepted, split_3042_accepted, split_3045_accepted, split_3047_accepted]
theorem split_batch_60_ok : split_batch_60_values.all id = true := by
  native_decide

def terminal_3007_accepted : Bool := LeafChecks.checkCore node_box_3007
def terminal_3019_accepted : Bool := LeafChecks.checkCore node_box_3019
def terminal_3021_accepted : Bool := LeafChecks.checkCore node_box_3021
def terminal_3025_accepted : Bool := LeafChecks.checkCore node_box_3025
def terminal_3027_accepted : Bool := LeafChecks.checkCore node_box_3027
def terminal_3043_accepted : Bool := LeafChecks.checkCore node_box_3043
def terminal_batch_60_values : List Bool := [terminal_3007_accepted, terminal_3019_accepted, terminal_3021_accepted, terminal_3025_accepted, terminal_3027_accepted, terminal_3043_accepted]
theorem terminal_batch_60_ok : terminal_batch_60_values.all id = true := by
  native_decide

theorem tree_3049 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3049) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3049] using leaf_3049_BranchSafe))⟩

theorem tree_3048 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3048) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3048] using leaf_3048_BranchSafe))⟩

theorem split_3047_ok : split_3047_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3047_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3047 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3047) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3047 node_box_3049 node_box_3050 ⟨4, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_3047_accepted] using split_3047_ok) tree_3049 tree_3050

theorem tree_3046 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3046) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3046] using leaf_3046_BranchSafe))⟩

theorem split_3045_ok : split_3045_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3045_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3045 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3045) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3045 node_box_3047 node_box_3048 ⟨7, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_3045_accepted] using split_3045_ok) tree_3047 tree_3048

theorem tree_3044 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3044) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3044] using leaf_3044_BranchSafe))⟩

theorem terminal_3043_ok : terminal_3043_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3043_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3043 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3043) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3043
  simpa [terminal_3043_accepted] using terminal_3043_ok

theorem split_3042_ok : split_3042_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3042_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3042 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3042) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3042 node_box_3043 node_box_3044 ⟨5, by omega⟩ ((1 : ℚ) / 160)
    (by simpa [split_3042_accepted] using split_3042_ok) tree_3043 tree_3044

theorem tree_3041 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3041) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3041] using leaf_3041_BranchSafe))⟩

theorem tree_3040 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3040) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3040] using leaf_3040_BranchSafe))⟩

theorem split_3039_ok : split_3039_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3039_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3039 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3039) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3039 node_box_3041 node_box_3042 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_3039_accepted] using split_3039_ok) tree_3041 tree_3042

theorem tree_3038 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3038) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3038] using leaf_3038_BranchSafe))⟩

theorem split_3037_ok : split_3037_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3037_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3037 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3037) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3037 node_box_3039 node_box_3040 ⟨7, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_3037_accepted] using split_3037_ok) tree_3039 tree_3040

theorem tree_3036 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3036) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3036] using leaf_3036_BranchSafe))⟩

theorem split_3035_ok : split_3035_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3035_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3035 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3035) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3035 node_box_3037 node_box_3038 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_3035_accepted] using split_3035_ok) tree_3037 tree_3038

theorem tree_3034 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3034) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3034] using leaf_3034_BranchSafe))⟩

theorem split_3033_ok : split_3033_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3033_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3033 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3033) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3033 node_box_3035 node_box_3036 ⟨3, by omega⟩ ((483 : ℚ) / 640)
    (by simpa [split_3033_accepted] using split_3033_ok) tree_3035 tree_3036

theorem split_3032_ok : split_3032_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3032_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3032 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3032) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3032 node_box_3033 node_box_3034 ⟨1, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_3032_accepted] using split_3032_ok) tree_3033 tree_3034

theorem tree_3031 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3031) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3031] using leaf_3031_BranchSafe))⟩

theorem split_3030_ok : split_3030_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3030_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3030 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3030) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3030 node_box_3031 node_box_3032 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_3030_accepted] using split_3030_ok) tree_3031 tree_3032

theorem tree_3029 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3029) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3029] using leaf_3029_BranchSafe))⟩

theorem tree_3028 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3028) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3028] using leaf_3028_BranchSafe))⟩

theorem terminal_3027_ok : terminal_3027_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3027_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3027 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3027) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3027
  simpa [terminal_3027_accepted] using terminal_3027_ok

theorem split_3026_ok : split_3026_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3026_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3026 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3026) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3026 node_box_3027 node_box_3028 ⟨1, by omega⟩ ((371 : ℚ) / 512)
    (by simpa [split_3026_accepted] using split_3026_ok) tree_3027 tree_3028

theorem terminal_3025_ok : terminal_3025_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3025_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3025 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3025) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3025
  simpa [terminal_3025_accepted] using terminal_3025_ok

theorem tree_3024 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3024) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3024] using leaf_3024_BranchSafe))⟩

theorem split_3023_ok : split_3023_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3023_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3023 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3023) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3023 node_box_3025 node_box_3026 ⟨3, by omega⟩ ((191 : ℚ) / 256)
    (by simpa [split_3023_accepted] using split_3023_ok) tree_3025 tree_3026

theorem tree_3022 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3022) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3022] using leaf_3022_BranchSafe))⟩

theorem terminal_3021_ok : terminal_3021_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3021_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3021 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3021) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3021
  simpa [terminal_3021_accepted] using terminal_3021_ok

theorem split_3020_ok : split_3020_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3020_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3020 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3020) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3020 node_box_3021 node_box_3022 ⟨1, by omega⟩ ((371 : ℚ) / 512)
    (by simpa [split_3020_accepted] using split_3020_ok) tree_3021 tree_3022

theorem terminal_3019_ok : terminal_3019_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3019_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3019 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3019) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3019
  simpa [terminal_3019_accepted] using terminal_3019_ok

theorem tree_3018 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3018) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3018] using leaf_3018_BranchSafe))⟩

theorem split_3017_ok : split_3017_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3017_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3017 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3017) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3017 node_box_3019 node_box_3020 ⟨3, by omega⟩ ((191 : ℚ) / 256)
    (by simpa [split_3017_accepted] using split_3017_ok) tree_3019 tree_3020

theorem split_3016_ok : split_3016_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3016_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3016 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3016) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3016 node_box_3017 node_box_3018 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_3016_accepted] using split_3016_ok) tree_3017 tree_3018

theorem tree_3015 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3015) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3015] using leaf_3015_BranchSafe))⟩

theorem split_3014_ok : split_3014_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3014_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3014 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3014) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3014 node_box_3023 node_box_3024 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_3014_accepted] using split_3014_ok) tree_3023 tree_3024

theorem split_3013_ok : split_3013_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3013_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3013 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3013) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3013 node_box_3015 node_box_3016 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_3013_accepted] using split_3013_ok) tree_3015 tree_3016

theorem tree_3012 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3012) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3012] using leaf_3012_BranchSafe))⟩

theorem split_3011_ok : split_3011_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3011_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3011 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3011) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3011 node_box_3013 node_box_3014 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_3011_accepted] using split_3011_ok) tree_3013 tree_3014

theorem tree_3010 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3010) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3010] using leaf_3010_BranchSafe))⟩

theorem split_3009_ok : split_3009_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3009_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3009 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3009) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3009 node_box_3011 node_box_3012 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_3009_accepted] using split_3009_ok) tree_3011 tree_3012

theorem tree_3008 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3008) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3008] using leaf_3008_BranchSafe))⟩

theorem terminal_3007_ok : terminal_3007_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_60_ok terminal_3007_accepted
    (by simp [terminal_batch_60_values])
  exact h
theorem tree_3007 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3007) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_3007
  simpa [terminal_3007_accepted] using terminal_3007_ok

theorem tree_3006 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3006) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3006] using leaf_3006_BranchSafe))⟩

theorem split_3005_ok : split_3005_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3005_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3005 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3005) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3005 node_box_3007 node_box_3008 ⟨3, by omega⟩ ((977 : ℚ) / 1280)
    (by simpa [split_3005_accepted] using split_3005_ok) tree_3007 tree_3008

theorem split_3004_ok : split_3004_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3004_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3004 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3004) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3004 node_box_3005 node_box_3006 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_3004_accepted] using split_3004_ok) tree_3005 tree_3006

theorem tree_3003 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3003) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3003] using leaf_3003_BranchSafe))⟩

theorem tree_3002 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3002) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3002] using leaf_3002_BranchSafe))⟩

theorem split_3001_ok : split_3001_accepted = true := by
  have h := List.all_eq_true.mp split_batch_60_ok split_3001_accepted
    (by simp [split_batch_60_values])
  exact h
theorem tree_3001 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3001) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3001 node_box_3003 node_box_3004 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_3001_accepted] using split_3001_ok) tree_3003 tree_3004

theorem tree_3000 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3000) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_3000] using leaf_3000_BranchSafe))⟩

#print axioms tree_3000
end PeaceableQueens.UpperBound.Generated.Even.Core
