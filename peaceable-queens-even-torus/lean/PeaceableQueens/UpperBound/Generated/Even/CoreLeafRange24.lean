import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange25
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled24Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_1200 : ProfileBox := branch_box_1200
def node_box_1201 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1202 : ProfileBox := branch_box_1202
def node_box_1203 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1204 : ProfileBox := branch_box_1204
def node_box_1205 : ProfileBox := branch_box_1205
def node_box_1206 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1207 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1208 : ProfileBox := { lower := ![(0 : ℚ) / 1, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1209 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (1 : ℚ) / 20, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1210 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (1087 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1211 : ProfileBox := { lower := ![(0 : ℚ) / 1, (79 : ℚ) / 128, (0 : ℚ) / 1, (1087 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (1591 : ℚ) / 2560, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1212 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1591 : ℚ) / 2560, (0 : ℚ) / 1, (1087 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (1 : ℚ) / 20, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1213 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1591 : ℚ) / 2560, (0 : ℚ) / 1, (1087 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (1 : ℚ) / 20, (437 : ℚ) / 512, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1214 : ProfileBox := branch_box_1214
def node_box_1215 : ProfileBox := { lower := ![(0 : ℚ) / 1, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1216 : ProfileBox := branch_box_1216
def node_box_1217 : ProfileBox := { lower := ![(0 : ℚ) / 1, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (1613 : ℚ) / 2560, (1 : ℚ) / 20, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1218 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1613 : ℚ) / 2560, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1219 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1613 : ℚ) / 2560, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (203 : ℚ) / 320, (1 : ℚ) / 20, (2163 : ℚ) / 2560, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1220 : ProfileBox := branch_box_1220
def node_box_1221 : ProfileBox := { lower := ![(1 : ℚ) / 40, (3 : ℚ) / 5, (0 : ℚ) / 1, (269 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1222 : ProfileBox := branch_box_1222
def node_box_1223 : ProfileBox := { lower := ![(1 : ℚ) / 40, (3 : ℚ) / 5, (0 : ℚ) / 1, (269 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1224 : ProfileBox := branch_box_1224
def node_box_1225 : ProfileBox := { lower := ![(1 : ℚ) / 40, (3 : ℚ) / 5, (0 : ℚ) / 1, (269 : ℚ) / 320, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1226 : ProfileBox := branch_box_1226
def node_box_1227 : ProfileBox := branch_box_1227
def node_box_1228 : ProfileBox := { lower := ![(1 : ℚ) / 40, (3 : ℚ) / 5, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1229 : ProfileBox := branch_box_1229
def node_box_1230 : ProfileBox := { lower := ![(1 : ℚ) / 40, (3 : ℚ) / 5, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1231 : ProfileBox := branch_box_1231
def node_box_1232 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1233 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1234 : ProfileBox := branch_box_1234
def node_box_1235 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1236 : ProfileBox := branch_box_1236
def node_box_1237 : ProfileBox := branch_box_1237
def node_box_1238 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1239 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (801 : ℚ) / 1280, (1 : ℚ) / 40, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1240 : ProfileBox := { lower := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (549 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1241 : ProfileBox := { lower := ![(1 : ℚ) / 40, (79 : ℚ) / 128, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (801 : ℚ) / 1280, (1 : ℚ) / 40, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1242 : ProfileBox := branch_box_1242
def node_box_1243 : ProfileBox := { lower := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (203 : ℚ) / 320, (1 : ℚ) / 40, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1244 : ProfileBox := branch_box_1244
def node_box_1245 : ProfileBox := { lower := ![(1 : ℚ) / 40, (801 : ℚ) / 1280, (0 : ℚ) / 1, (269 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (1613 : ℚ) / 2560, (1 : ℚ) / 40, (1087 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_1246 : ProfileBox := branch_box_1246
def node_box_1247 : ProfileBox := { lower := ![(0 : ℚ) / 1, (203 : ℚ) / 320, (0 : ℚ) / 1, (129 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (1 : ℚ) / 20, (269 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_1248 : ProfileBox := branch_box_1248
def node_box_1249 : ProfileBox := { lower := ![(0 : ℚ) / 1, (203 : ℚ) / 320, (0 : ℚ) / 1, (129 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (107 : ℚ) / 160, (1 : ℚ) / 20, (269 : ℚ) / 320, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }

def split_1201_accepted : Bool := splitNodeOK node_box_1201 node_box_1203 node_box_1204 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_1203_accepted : Bool := splitNodeOK node_box_1203 node_box_1205 node_box_1206 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_1206_accepted : Bool := splitNodeOK node_box_1206 node_box_1207 node_box_1208 ⟨1, by omega⟩ ((801 : ℚ) / 1280)
def split_1207_accepted : Bool := splitNodeOK node_box_1207 node_box_1209 node_box_1210 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
def split_1208_accepted : Bool := splitNodeOK node_box_1208 node_box_1215 node_box_1216 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
def split_1210_accepted : Bool := splitNodeOK node_box_1210 node_box_1211 node_box_1212 ⟨1, by omega⟩ ((1591 : ℚ) / 2560)
def split_1212_accepted : Bool := splitNodeOK node_box_1212 node_box_1213 node_box_1214 ⟨3, by omega⟩ ((437 : ℚ) / 512)
def split_1215_accepted : Bool := splitNodeOK node_box_1215 node_box_1217 node_box_1218 ⟨1, by omega⟩ ((1613 : ℚ) / 2560)
def split_1218_accepted : Bool := splitNodeOK node_box_1218 node_box_1219 node_box_1220 ⟨3, by omega⟩ ((2163 : ℚ) / 2560)
def split_1221_accepted : Bool := splitNodeOK node_box_1221 node_box_1223 node_box_1224 ⟨5, by omega⟩ ((1 : ℚ) / 40)
def split_1223_accepted : Bool := splitNodeOK node_box_1223 node_box_1225 node_box_1226 ⟨7, by omega⟩ ((1 : ℚ) / 40)
def split_1225_accepted : Bool := splitNodeOK node_box_1225 node_box_1227 node_box_1228 ⟨4, by omega⟩ ((39 : ℚ) / 40)
def split_1228_accepted : Bool := splitNodeOK node_box_1228 node_box_1229 node_box_1230 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_1230_accepted : Bool := splitNodeOK node_box_1230 node_box_1231 node_box_1232 ⟨1, by omega⟩ ((79 : ℚ) / 128)
def split_1232_accepted : Bool := splitNodeOK node_box_1232 node_box_1233 node_box_1234 ⟨3, by omega⟩ ((549 : ℚ) / 640)
def split_1233_accepted : Bool := splitNodeOK node_box_1233 node_box_1235 node_box_1236 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_1235_accepted : Bool := splitNodeOK node_box_1235 node_box_1237 node_box_1238 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_1238_accepted : Bool := splitNodeOK node_box_1238 node_box_1239 node_box_1240 ⟨1, by omega⟩ ((801 : ℚ) / 1280)
def split_1239_accepted : Bool := splitNodeOK node_box_1239 node_box_1241 node_box_1242 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
def split_1240_accepted : Bool := splitNodeOK node_box_1240 node_box_1243 node_box_1244 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
def split_1243_accepted : Bool := splitNodeOK node_box_1243 node_box_1245 node_box_1246 ⟨1, by omega⟩ ((1613 : ℚ) / 2560)
def split_1247_accepted : Bool := splitNodeOK node_box_1247 node_box_1249 node_box_1250 ⟨0, by omega⟩ ((1 : ℚ) / 40)
def split_1249_accepted : Bool := splitNodeOK node_box_1249 node_box_1251 node_box_1252 ⟨5, by omega⟩ ((1 : ℚ) / 40)
def split_batch_24_values : List Bool := [split_1201_accepted, split_1203_accepted, split_1206_accepted, split_1207_accepted, split_1208_accepted, split_1210_accepted, split_1212_accepted, split_1215_accepted, split_1218_accepted, split_1221_accepted, split_1223_accepted, split_1225_accepted, split_1228_accepted, split_1230_accepted, split_1232_accepted, split_1233_accepted, split_1235_accepted, split_1238_accepted, split_1239_accepted, split_1240_accepted, split_1243_accepted, split_1247_accepted, split_1249_accepted]
theorem split_batch_24_ok : split_batch_24_values.all id = true := by
  native_decide

def terminal_1209_accepted : Bool := LeafChecks.checkCore node_box_1209
def terminal_1211_accepted : Bool := LeafChecks.checkCore node_box_1211
def terminal_1213_accepted : Bool := LeafChecks.checkCore node_box_1213
def terminal_1217_accepted : Bool := LeafChecks.checkCore node_box_1217
def terminal_1219_accepted : Bool := LeafChecks.checkCore node_box_1219
def terminal_1241_accepted : Bool := LeafChecks.checkCore node_box_1241
def terminal_1245_accepted : Bool := LeafChecks.checkCore node_box_1245
def terminal_batch_24_values : List Bool := [terminal_1209_accepted, terminal_1211_accepted, terminal_1213_accepted, terminal_1217_accepted, terminal_1219_accepted, terminal_1241_accepted, terminal_1245_accepted]
theorem terminal_batch_24_ok : terminal_batch_24_values.all id = true := by
  native_decide

theorem split_1249_ok : split_1249_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1249_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1249 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1249) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1249 node_box_1251 node_box_1252 ⟨5, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1249_accepted] using split_1249_ok) tree_1251 tree_1252

theorem tree_1248 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1248) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1248] using leaf_1248_BranchSafe))⟩

theorem split_1247_ok : split_1247_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1247_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1247 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1247) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1247 node_box_1249 node_box_1250 ⟨0, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1247_accepted] using split_1247_ok) tree_1249 tree_1250

theorem tree_1246 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1246) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1246] using leaf_1246_BranchSafe))⟩

theorem terminal_1245_ok : terminal_1245_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1245_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1245 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1245) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1245
  simpa [terminal_1245_accepted] using terminal_1245_ok

theorem tree_1244 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1244) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1244] using leaf_1244_BranchSafe))⟩

theorem split_1243_ok : split_1243_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1243_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1243 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1243) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1243 node_box_1245 node_box_1246 ⟨1, by omega⟩ ((1613 : ℚ) / 2560)
    (by simpa [split_1243_accepted] using split_1243_ok) tree_1245 tree_1246

theorem tree_1242 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1242) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1242] using leaf_1242_BranchSafe))⟩

theorem terminal_1241_ok : terminal_1241_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1241_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1241 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1241) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1241
  simpa [terminal_1241_accepted] using terminal_1241_ok

theorem split_1240_ok : split_1240_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1240_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1240 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1240) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1240 node_box_1243 node_box_1244 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
    (by simpa [split_1240_accepted] using split_1240_ok) tree_1243 tree_1244

theorem split_1239_ok : split_1239_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1239_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1239 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1239) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1239 node_box_1241 node_box_1242 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
    (by simpa [split_1239_accepted] using split_1239_ok) tree_1241 tree_1242

theorem split_1238_ok : split_1238_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1238_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1238 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1238) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1238 node_box_1239 node_box_1240 ⟨1, by omega⟩ ((801 : ℚ) / 1280)
    (by simpa [split_1238_accepted] using split_1238_ok) tree_1239 tree_1240

theorem tree_1237 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1237) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1237] using leaf_1237_BranchSafe))⟩

theorem tree_1236 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1236) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1236] using leaf_1236_BranchSafe))⟩

theorem split_1235_ok : split_1235_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1235_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1235 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1235) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1235 node_box_1237 node_box_1238 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_1235_accepted] using split_1235_ok) tree_1237 tree_1238

theorem tree_1234 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1234) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1234] using leaf_1234_BranchSafe))⟩

theorem split_1233_ok : split_1233_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1233_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1233 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1233) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1233 node_box_1235 node_box_1236 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1233_accepted] using split_1233_ok) tree_1235 tree_1236

theorem split_1232_ok : split_1232_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1232_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1232 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1232) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1232 node_box_1233 node_box_1234 ⟨3, by omega⟩ ((549 : ℚ) / 640)
    (by simpa [split_1232_accepted] using split_1232_ok) tree_1233 tree_1234

theorem tree_1231 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1231) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1231] using leaf_1231_BranchSafe))⟩

theorem split_1230_ok : split_1230_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1230_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1230 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1230) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1230 node_box_1231 node_box_1232 ⟨1, by omega⟩ ((79 : ℚ) / 128)
    (by simpa [split_1230_accepted] using split_1230_ok) tree_1231 tree_1232

theorem tree_1229 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1229) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1229] using leaf_1229_BranchSafe))⟩

theorem split_1228_ok : split_1228_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1228_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1228 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1228) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1228 node_box_1229 node_box_1230 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_1228_accepted] using split_1228_ok) tree_1229 tree_1230

theorem tree_1227 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1227) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1227] using leaf_1227_BranchSafe))⟩

theorem tree_1226 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1226) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1226] using leaf_1226_BranchSafe))⟩

theorem split_1225_ok : split_1225_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1225_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1225 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1225) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1225 node_box_1227 node_box_1228 ⟨4, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_1225_accepted] using split_1225_ok) tree_1227 tree_1228

theorem tree_1224 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1224) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1224] using leaf_1224_BranchSafe))⟩

theorem split_1223_ok : split_1223_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1223_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1223 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1223) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1223 node_box_1225 node_box_1226 ⟨7, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1223_accepted] using split_1223_ok) tree_1225 tree_1226

theorem tree_1222 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1222) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1222] using leaf_1222_BranchSafe))⟩

theorem split_1221_ok : split_1221_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1221_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1221 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1221) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1221 node_box_1223 node_box_1224 ⟨5, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_1221_accepted] using split_1221_ok) tree_1223 tree_1224

theorem tree_1220 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1220) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1220] using leaf_1220_BranchSafe))⟩

theorem terminal_1219_ok : terminal_1219_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1219_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1219 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1219) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1219
  simpa [terminal_1219_accepted] using terminal_1219_ok

theorem split_1218_ok : split_1218_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1218_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1218 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1218) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1218 node_box_1219 node_box_1220 ⟨3, by omega⟩ ((2163 : ℚ) / 2560)
    (by simpa [split_1218_accepted] using split_1218_ok) tree_1219 tree_1220

theorem terminal_1217_ok : terminal_1217_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1217_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1217 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1217) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1217
  simpa [terminal_1217_accepted] using terminal_1217_ok

theorem tree_1216 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1216) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1216] using leaf_1216_BranchSafe))⟩

theorem split_1215_ok : split_1215_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1215_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1215 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1215) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1215 node_box_1217 node_box_1218 ⟨1, by omega⟩ ((1613 : ℚ) / 2560)
    (by simpa [split_1215_accepted] using split_1215_ok) tree_1217 tree_1218

theorem tree_1214 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1214) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1214] using leaf_1214_BranchSafe))⟩

theorem terminal_1213_ok : terminal_1213_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1213_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1213 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1213) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1213
  simpa [terminal_1213_accepted] using terminal_1213_ok

theorem split_1212_ok : split_1212_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1212_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1212 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1212) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1212 node_box_1213 node_box_1214 ⟨3, by omega⟩ ((437 : ℚ) / 512)
    (by simpa [split_1212_accepted] using split_1212_ok) tree_1213 tree_1214

theorem terminal_1211_ok : terminal_1211_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1211_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1211 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1211) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1211
  simpa [terminal_1211_accepted] using terminal_1211_ok

theorem split_1210_ok : split_1210_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1210_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1210 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1210) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1210 node_box_1211 node_box_1212 ⟨1, by omega⟩ ((1591 : ℚ) / 2560)
    (by simpa [split_1210_accepted] using split_1210_ok) tree_1211 tree_1212

theorem terminal_1209_ok : terminal_1209_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_24_ok terminal_1209_accepted
    (by simp [terminal_batch_24_values])
  exact h
theorem tree_1209 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1209) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_1209
  simpa [terminal_1209_accepted] using terminal_1209_ok

theorem split_1208_ok : split_1208_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1208_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1208 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1208) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1208 node_box_1215 node_box_1216 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
    (by simpa [split_1208_accepted] using split_1208_ok) tree_1215 tree_1216

theorem split_1207_ok : split_1207_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1207_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1207 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1207) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1207 node_box_1209 node_box_1210 ⟨3, by omega⟩ ((1087 : ℚ) / 1280)
    (by simpa [split_1207_accepted] using split_1207_ok) tree_1209 tree_1210

theorem split_1206_ok : split_1206_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1206_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1206 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1206) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1206 node_box_1207 node_box_1208 ⟨1, by omega⟩ ((801 : ℚ) / 1280)
    (by simpa [split_1206_accepted] using split_1206_ok) tree_1207 tree_1208

theorem tree_1205 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1205) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1205] using leaf_1205_BranchSafe))⟩

theorem tree_1204 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1204) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1204] using leaf_1204_BranchSafe))⟩

theorem split_1203_ok : split_1203_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1203_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1203 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1203) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1203 node_box_1205 node_box_1206 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_1203_accepted] using split_1203_ok) tree_1205 tree_1206

theorem tree_1202 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1202) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1202] using leaf_1202_BranchSafe))⟩

theorem split_1201_ok : split_1201_accepted = true := by
  have h := List.all_eq_true.mp split_batch_24_ok split_1201_accepted
    (by simp [split_batch_24_values])
  exact h
theorem tree_1201 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1201) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1201 node_box_1203 node_box_1204 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_1201_accepted] using split_1201_ok) tree_1203 tree_1204

theorem tree_1200 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1200) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_1200] using leaf_1200_BranchSafe))⟩

#print axioms tree_1200
end PeaceableQueens.UpperBound.Generated.Even.Core
