import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange09
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled08Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_400 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_401 : ProfileBox := branch_box_401
def node_box_402 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 40, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_403 : ProfileBox := branch_box_403
def node_box_404 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 40, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_405 : ProfileBox := branch_box_405
def node_box_406 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_407 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_408 : ProfileBox := branch_box_408
def node_box_409 : ProfileBox := branch_box_409
def node_box_410 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_411 : ProfileBox := branch_box_411
def node_box_412 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 80, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_413 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 80, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (911 : ℚ) / 1280, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_414 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 80, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_415 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 80, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_416 : ProfileBox := { lower := ![(7 : ℚ) / 160, (933 : ℚ) / 1280, (3 : ℚ) / 80, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_417 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 80, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (7 : ℚ) / 160, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_418 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (7 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_419 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (7 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(13 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_420 : ProfileBox := branch_box_420
def node_box_421 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (7 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(13 : ℚ) / 320, (59 : ℚ) / 80, (3 : ℚ) / 64, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_422 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 64, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(13 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_423 : ProfileBox := { lower := ![(3 : ℚ) / 80, (933 : ℚ) / 1280, (3 : ℚ) / 64, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(5 : ℚ) / 128, (59 : ℚ) / 80, (1 : ℚ) / 20, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_424 : ProfileBox := branch_box_424
def node_box_425 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_426 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_427 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_428 : ProfileBox := branch_box_428
def node_box_429 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_430 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_431 : ProfileBox := branch_box_431
def node_box_432 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_433 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_434 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_435 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_436 : ProfileBox := branch_box_436
def node_box_437 : ProfileBox := branch_box_437
def node_box_438 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 40, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_439 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_440 : ProfileBox := branch_box_440
def node_box_441 : ProfileBox := branch_box_441
def node_box_442 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_443 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_444 : ProfileBox := { lower := ![(7 : ℚ) / 160, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_445 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (3 : ℚ) / 80, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_446 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (7 : ℚ) / 160, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_447 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (7 : ℚ) / 160, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(13 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_448 : ProfileBox := { lower := ![(13 : ℚ) / 320, (461 : ℚ) / 640, (7 : ℚ) / 160, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(7 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_449 : ProfileBox := { lower := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (7 : ℚ) / 160, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(13 : ℚ) / 320, (59 : ℚ) / 80, (3 : ℚ) / 64, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }

def split_400_accepted : Bool := splitNodeOK node_box_400 node_box_401 node_box_402 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
def split_402_accepted : Bool := splitNodeOK node_box_402 node_box_403 node_box_404 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
def split_406_accepted : Bool := splitNodeOK node_box_406 node_box_407 node_box_408 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_407_accepted : Bool := splitNodeOK node_box_407 node_box_409 node_box_410 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_410_accepted : Bool := splitNodeOK node_box_410 node_box_411 node_box_412 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
def split_412_accepted : Bool := splitNodeOK node_box_412 node_box_413 node_box_414 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
def split_414_accepted : Bool := splitNodeOK node_box_414 node_box_415 node_box_416 ⟨0, by omega⟩ ((7 : ℚ) / 160)
def split_415_accepted : Bool := splitNodeOK node_box_415 node_box_417 node_box_418 ⟨2, by omega⟩ ((7 : ℚ) / 160)
def split_418_accepted : Bool := splitNodeOK node_box_418 node_box_419 node_box_420 ⟨0, by omega⟩ ((13 : ℚ) / 320)
def split_419_accepted : Bool := splitNodeOK node_box_419 node_box_421 node_box_422 ⟨2, by omega⟩ ((3 : ℚ) / 64)
def split_422_accepted : Bool := splitNodeOK node_box_422 node_box_423 node_box_424 ⟨0, by omega⟩ ((5 : ℚ) / 128)
def split_425_accepted : Bool := splitNodeOK node_box_425 node_box_427 node_box_428 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_426_accepted : Bool := splitNodeOK node_box_426 node_box_433 node_box_434 ⟨2, by omega⟩ ((3 : ℚ) / 80)
def split_427_accepted : Bool := splitNodeOK node_box_427 node_box_429 node_box_430 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_429_accepted : Bool := splitNodeOK node_box_429 node_box_431 node_box_432 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_433_accepted : Bool := splitNodeOK node_box_433 node_box_435 node_box_436 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_434_accepted : Bool := splitNodeOK node_box_434 node_box_439 node_box_440 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_435_accepted : Bool := splitNodeOK node_box_435 node_box_437 node_box_438 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_439_accepted : Bool := splitNodeOK node_box_439 node_box_441 node_box_442 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_442_accepted : Bool := splitNodeOK node_box_442 node_box_443 node_box_444 ⟨0, by omega⟩ ((7 : ℚ) / 160)
def split_443_accepted : Bool := splitNodeOK node_box_443 node_box_445 node_box_446 ⟨2, by omega⟩ ((7 : ℚ) / 160)
def split_444_accepted : Bool := splitNodeOK node_box_444 node_box_461 node_box_462 ⟨2, by omega⟩ ((7 : ℚ) / 160)
def split_446_accepted : Bool := splitNodeOK node_box_446 node_box_447 node_box_448 ⟨0, by omega⟩ ((13 : ℚ) / 320)
def split_447_accepted : Bool := splitNodeOK node_box_447 node_box_449 node_box_450 ⟨2, by omega⟩ ((3 : ℚ) / 64)
def split_448_accepted : Bool := splitNodeOK node_box_448 node_box_455 node_box_456 ⟨2, by omega⟩ ((3 : ℚ) / 64)
def split_batch_08_values : List Bool := [split_400_accepted, split_402_accepted, split_406_accepted, split_407_accepted, split_410_accepted, split_412_accepted, split_414_accepted, split_415_accepted, split_418_accepted, split_419_accepted, split_422_accepted, split_425_accepted, split_426_accepted, split_427_accepted, split_429_accepted, split_433_accepted, split_434_accepted, split_435_accepted, split_439_accepted, split_442_accepted, split_443_accepted, split_444_accepted, split_446_accepted, split_447_accepted, split_448_accepted]
theorem split_batch_08_ok : split_batch_08_values.all id = true := by
  native_decide

def terminal_404_accepted : Bool := LeafChecks.checkCore node_box_404
def terminal_413_accepted : Bool := LeafChecks.checkEmpty .rowColumnSum node_box_413
def terminal_416_accepted : Bool := LeafChecks.checkEmpty .rowColumnSum node_box_416
def terminal_417_accepted : Bool := LeafChecks.checkEmpty .rowColumnSum node_box_417
def terminal_421_accepted : Bool := LeafChecks.checkCore node_box_421
def terminal_423_accepted : Bool := LeafChecks.checkCore node_box_423
def terminal_430_accepted : Bool := LeafChecks.checkCore node_box_430
def terminal_432_accepted : Bool := LeafChecks.checkCore node_box_432
def terminal_438_accepted : Bool := LeafChecks.checkCore node_box_438
def terminal_445_accepted : Bool := LeafChecks.checkCore node_box_445
def terminal_449_accepted : Bool := LeafChecks.checkCore node_box_449
def terminal_batch_08_values : List Bool := [terminal_404_accepted, terminal_413_accepted, terminal_416_accepted, terminal_417_accepted, terminal_421_accepted, terminal_423_accepted, terminal_430_accepted, terminal_432_accepted, terminal_438_accepted, terminal_445_accepted, terminal_449_accepted]
theorem terminal_batch_08_ok : terminal_batch_08_values.all id = true := by
  native_decide

theorem terminal_449_ok : terminal_449_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_449_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_449 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_449) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_449
  simpa [terminal_449_accepted] using terminal_449_ok

theorem split_448_ok : split_448_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_448_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_448 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_448) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_448 node_box_455 node_box_456 ⟨2, by omega⟩ ((3 : ℚ) / 64)
    (by simpa [split_448_accepted] using split_448_ok) tree_455 tree_456

theorem split_447_ok : split_447_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_447_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_447 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_447) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_447 node_box_449 node_box_450 ⟨2, by omega⟩ ((3 : ℚ) / 64)
    (by simpa [split_447_accepted] using split_447_ok) tree_449 tree_450

theorem split_446_ok : split_446_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_446_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_446 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_446) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_446 node_box_447 node_box_448 ⟨0, by omega⟩ ((13 : ℚ) / 320)
    (by simpa [split_446_accepted] using split_446_ok) tree_447 tree_448

theorem terminal_445_ok : terminal_445_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_445_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_445 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_445) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_445
  simpa [terminal_445_accepted] using terminal_445_ok

theorem split_444_ok : split_444_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_444_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_444 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_444) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_444 node_box_461 node_box_462 ⟨2, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_444_accepted] using split_444_ok) tree_461 tree_462

theorem split_443_ok : split_443_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_443_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_443 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_443) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_443 node_box_445 node_box_446 ⟨2, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_443_accepted] using split_443_ok) tree_445 tree_446

theorem split_442_ok : split_442_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_442_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_442 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_442) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_442 node_box_443 node_box_444 ⟨0, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_442_accepted] using split_442_ok) tree_443 tree_444

theorem tree_441 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_441) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_441] using leaf_441_BranchSafe))⟩

theorem tree_440 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_440) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_440] using leaf_440_BranchSafe))⟩

theorem split_439_ok : split_439_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_439_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_439 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_439) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_439 node_box_441 node_box_442 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_439_accepted] using split_439_ok) tree_441 tree_442

theorem terminal_438_ok : terminal_438_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_438_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_438 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_438) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_438
  simpa [terminal_438_accepted] using terminal_438_ok

theorem tree_437 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_437) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_437] using leaf_437_BranchSafe))⟩

theorem tree_436 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_436) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_436] using leaf_436_BranchSafe))⟩

theorem split_435_ok : split_435_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_435_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_435 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_435) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_435 node_box_437 node_box_438 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_435_accepted] using split_435_ok) tree_437 tree_438

theorem split_434_ok : split_434_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_434_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_434 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_434) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_434 node_box_439 node_box_440 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_434_accepted] using split_434_ok) tree_439 tree_440

theorem split_433_ok : split_433_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_433_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_433 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_433) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_433 node_box_435 node_box_436 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_433_accepted] using split_433_ok) tree_435 tree_436

theorem terminal_432_ok : terminal_432_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_432_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_432 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_432) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_432
  simpa [terminal_432_accepted] using terminal_432_ok

theorem tree_431 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_431) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_431] using leaf_431_BranchSafe))⟩

theorem terminal_430_ok : terminal_430_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_430_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_430 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_430) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_430
  simpa [terminal_430_accepted] using terminal_430_ok

theorem split_429_ok : split_429_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_429_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_429 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_429) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_429 node_box_431 node_box_432 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_429_accepted] using split_429_ok) tree_431 tree_432

theorem tree_428 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_428) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_428] using leaf_428_BranchSafe))⟩

theorem split_427_ok : split_427_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_427_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_427 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_427) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_427 node_box_429 node_box_430 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_427_accepted] using split_427_ok) tree_429 tree_430

theorem split_426_ok : split_426_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_426_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_426 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_426) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_426 node_box_433 node_box_434 ⟨2, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_426_accepted] using split_426_ok) tree_433 tree_434

theorem split_425_ok : split_425_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_425_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_425 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_425) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_425 node_box_427 node_box_428 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_425_accepted] using split_425_ok) tree_427 tree_428

theorem tree_424 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_424) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_424] using leaf_424_BranchSafe))⟩

theorem terminal_423_ok : terminal_423_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_423_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_423 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_423) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_423
  simpa [terminal_423_accepted] using terminal_423_ok

theorem split_422_ok : split_422_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_422_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_422 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_422) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_422 node_box_423 node_box_424 ⟨0, by omega⟩ ((5 : ℚ) / 128)
    (by simpa [split_422_accepted] using split_422_ok) tree_423 tree_424

theorem terminal_421_ok : terminal_421_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_421_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_421 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_421) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_421
  simpa [terminal_421_accepted] using terminal_421_ok

theorem tree_420 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_420) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_420] using leaf_420_BranchSafe))⟩

theorem split_419_ok : split_419_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_419_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_419 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_419) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_419 node_box_421 node_box_422 ⟨2, by omega⟩ ((3 : ℚ) / 64)
    (by simpa [split_419_accepted] using split_419_ok) tree_421 tree_422

theorem split_418_ok : split_418_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_418_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_418 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_418) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_418 node_box_419 node_box_420 ⟨0, by omega⟩ ((13 : ℚ) / 320)
    (by simpa [split_418_accepted] using split_418_ok) tree_419 tree_420

theorem terminal_417_ok : terminal_417_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_417_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_417 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_417) := by
  refine ⟨CoverTree.leaf (Or.inl (Or.inr ?_))⟩
  apply LeafChecks.checkEmpty_sound .rowColumnSum node_box_417
  simpa [terminal_417_accepted] using terminal_417_ok

theorem terminal_416_ok : terminal_416_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_416_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_416 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_416) := by
  refine ⟨CoverTree.leaf (Or.inl (Or.inr ?_))⟩
  apply LeafChecks.checkEmpty_sound .rowColumnSum node_box_416
  simpa [terminal_416_accepted] using terminal_416_ok

theorem split_415_ok : split_415_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_415_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_415 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_415) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_415 node_box_417 node_box_418 ⟨2, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_415_accepted] using split_415_ok) tree_417 tree_418

theorem split_414_ok : split_414_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_414_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_414 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_414) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_414 node_box_415 node_box_416 ⟨0, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_414_accepted] using split_414_ok) tree_415 tree_416

theorem terminal_413_ok : terminal_413_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_413_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_413 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_413) := by
  refine ⟨CoverTree.leaf (Or.inl (Or.inr ?_))⟩
  apply LeafChecks.checkEmpty_sound .rowColumnSum node_box_413
  simpa [terminal_413_accepted] using terminal_413_ok

theorem split_412_ok : split_412_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_412_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_412 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_412) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_412 node_box_413 node_box_414 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_412_accepted] using split_412_ok) tree_413 tree_414

theorem tree_411 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_411) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_411] using leaf_411_BranchSafe))⟩

theorem split_410_ok : split_410_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_410_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_410 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_410) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_410 node_box_411 node_box_412 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_410_accepted] using split_410_ok) tree_411 tree_412

theorem tree_409 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_409) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_409] using leaf_409_BranchSafe))⟩

theorem tree_408 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_408) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_408] using leaf_408_BranchSafe))⟩

theorem split_407_ok : split_407_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_407_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_407 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_407) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_407 node_box_409 node_box_410 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_407_accepted] using split_407_ok) tree_409 tree_410

theorem split_406_ok : split_406_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_406_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_406 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_406) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_406 node_box_407 node_box_408 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_406_accepted] using split_406_ok) tree_407 tree_408

theorem tree_405 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_405) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_405] using leaf_405_BranchSafe))⟩

theorem terminal_404_ok : terminal_404_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_08_ok terminal_404_accepted
    (by simp [terminal_batch_08_values])
  exact h
theorem tree_404 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_404) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_404
  simpa [terminal_404_accepted] using terminal_404_ok

theorem tree_403 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_403) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_403] using leaf_403_BranchSafe))⟩

theorem split_402_ok : split_402_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_402_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_402 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_402) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_402 node_box_403 node_box_404 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_402_accepted] using split_402_ok) tree_403 tree_404

theorem tree_401 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_401) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_401] using leaf_401_BranchSafe))⟩

theorem split_400_ok : split_400_accepted = true := by
  have h := List.all_eq_true.mp split_batch_08_ok split_400_accepted
    (by simp [split_batch_08_values])
  exact h
theorem tree_400 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_400) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_400 node_box_401 node_box_402 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_400_accepted] using split_400_ok) tree_401 tree_402

#print axioms tree_400
end PeaceableQueens.UpperBound.Generated.Even.Core
