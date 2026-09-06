import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_2151 : Box := { S := 3564800, lo := ![0, 2475865, 0, 2751580, 3497960, 0, 3475680, 0], hi := ![89120, 2506500, 178240, 2782215, 3520240, 44560, 3497960, 89120] }
def cert_2151 : Certificate := {
  mu := [(⟨4, by omega⟩, -796320), (⟨5, by omega⟩, -2048000), (⟨6, by omega⟩, -1516800), (⟨9, by omega⟩, -2048000), (⟨21, by omega⟩, -1516800), (⟨33, by omega⟩, -1516800), (⟨37, by omega⟩, -2048000), (⟨42, by omega⟩, -2048000), (⟨50, by omega⟩, -2048000), (⟨53, by omega⟩, -1516800), (⟨70, by omega⟩, -1516800), (⟨74, by omega⟩, -2048000), (⟨82, by omega⟩, -2048000), (⟨86, by omega⟩, -1516800), (⟨90, by omega⟩, -4096000), (⟨94, by omega⟩, -1062400)]
  nu := [(⟨0, by omega⟩, -2048000), (⟨3, by omega⟩, 2048000), (⟨4, by omega⟩, 2048000), (⟨5, by omega⟩, -2048000), (⟨10, by omega⟩, -1516800), (⟨12, by omega⟩, 1516800), (⟨14, by omega⟩, 1516800), (⟨16, by omega⟩, -1516800), (⟨19, by omega⟩, -1516800), (⟨20, by omega⟩, -1516800), (⟨21, by omega⟩, 1516800), (⟨22, by omega⟩, 1516800), (⟨24, by omega⟩, 1516800), (⟨25, by omega⟩, -1516800), (⟨27, by omega⟩, -1516800), (⟨29, by omega⟩, -1516800), (⟨30, by omega⟩, -6144000), (⟨31, by omega⟩, 4096000), (⟨32, by omega⟩, 4096000), (⟨33, by omega⟩, 4096000), (⟨34, by omega⟩, 4096000), (⟨35, by omega⟩, -2048000), (⟨36, by omega⟩, -2048000), (⟨37, by omega⟩, -2048000), (⟨38, by omega⟩, -2048000), (⟨39, by omega⟩, -2048000), (⟨40, by omega⟩, -2048000), (⟨41, by omega⟩, -531200)]
  claimed := 23806828844933120000
}
def branch_box_2151 : RatBox 8 := { lower := box_2151.profileLo, upper := box_2151.profileHi }
def accepted_2151 : Bool := checkAt 527 1000 box_2151 cert_2151

def box_2156 : Box := { S := 41936486400, lo := ![0, 29306396160, 0, 32549921280, 41150177280, 0, 41150177280, 0], hi := ![1048412160, 29486592000, 2096824320, 32730117120, 41412280320, 524206080, 41412280320, 1048412160] }
def cert_2156 : Certificate := {
  mu := [(⟨5, by omega⟩, -2588672000), (⟨6, by omega⟩, -39347814400), (⟨9, by omega⟩, -2588672000), (⟨21, by omega⟩, -2588672000), (⟨34, by omega⟩, -2588672000), (⟨37, by omega⟩, -2588672000), (⟨42, by omega⟩, -2588672000), (⟨46, by omega⟩, -39347814400), (⟨50, by omega⟩, -2588672000), (⟨62, by omega⟩, -1897472000), (⟨74, by omega⟩, -2588672000), (⟨82, by omega⟩, -2588672000), (⟨89, by omega⟩, -39347814400), (⟨90, by omega⟩, -39347814400)]
  nu := [(⟨0, by omega⟩, -39347814400), (⟨3, by omega⟩, 39347814400), (⟨4, by omega⟩, 39347814400), (⟨5, by omega⟩, -2588672000), (⟨10, by omega⟩, -39347814400), (⟨12, by omega⟩, 39347814400), (⟨16, by omega⟩, -2588672000), (⟨20, by omega⟩, -39347814400), (⟨21, by omega⟩, 39347814400), (⟨22, by omega⟩, 1897472000), (⟨23, by omega⟩, 39347814400), (⟨25, by omega⟩, -2588672000), (⟨26, by omega⟩, -39347814400), (⟨28, by omega⟩, -1897472000), (⟨30, by omega⟩, -44525158400), (⟨31, by omega⟩, 5177344000), (⟨32, by omega⟩, 5177344000), (⟨33, by omega⟩, 41936486400), (⟨34, by omega⟩, 41936486400), (⟨35, by omega⟩, -2588672000), (⟨36, by omega⟩, -2588672000), (⟨37, by omega⟩, -2588672000), (⟨38, by omega⟩, -2588672000), (⟨39, by omega⟩, -2588672000), (⟨40, by omega⟩, -39347814400)]
  claimed := 38766833894311180842534174720000
}
def branch_box_2156 : RatBox 8 := { lower := box_2156.profileLo, upper := box_2156.profileHi }
def accepted_2156 : Bool := checkAt 527 1000 box_2156 cert_2156

def box_2164 : Box := { S := 103940096000, lo := ![0, 71743027200, 0, 81568614400, 101341593600, 0, 102640844800, 0], hi := ![2598502400, 72189644800, 5197004800, 82015232000, 102640844800, 1299251200, 103940096000, 2598502400] }
def cert_2164 : Certificate := {
  mu := [(⟨5, by omega⟩, -5197004800), (⟨6, by omega⟩, -98743091200), (⟨9, by omega⟩, -5197004800), (⟨21, by omega⟩, -5197004800), (⟨34, by omega⟩, -629145600), (⟨37, by omega⟩, -5197004800), (⟨42, by omega⟩, -5197004800), (⟨46, by omega⟩, -419430400), (⟨50, by omega⟩, -5197004800), (⟨62, by omega⟩, -5197004800), (⟨74, by omega⟩, -5197004800), (⟨82, by omega⟩, -5197004800), (⟨89, by omega⟩, -197486182400)]
  nu := [(⟨0, by omega⟩, -98743091200), (⟨3, by omega⟩, 98743091200), (⟨4, by omega⟩, 98743091200), (⟨5, by omega⟩, -5197004800), (⟨10, by omega⟩, -98743091200), (⟨12, by omega⟩, 98743091200), (⟨16, by omega⟩, -5197004800), (⟨20, by omega⟩, -98743091200), (⟨21, by omega⟩, 98743091200), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -5197004800), (⟨30, by omega⟩, -109137100800), (⟨31, by omega⟩, 10394009600), (⟨32, by omega⟩, 10394009600), (⟨33, by omega⟩, 103940096000), (⟨34, by omega⟩, 103940096000), (⟨35, by omega⟩, -5197004800), (⟨36, by omega⟩, -5197004800), (⟨37, by omega⟩, -5197004800), (⟨38, by omega⟩, -5197004800), (⟨39, by omega⟩, -5197004800), (⟨40, by omega⟩, -98743091200)]
  claimed := 590136422854421890610495488000000
}
def branch_box_2164 : RatBox 8 := { lower := box_2164.profileLo, upper := box_2164.profileHi }
def accepted_2164 : Bool := checkAt 527 1000 box_2164 cert_2164

def box_2166 : Box := { S := 12812288000, lo := ![0, 8898534400, 0, 9999590400, 12491980800, 0, 12652134400, 0], hi := ![320307200, 9008640000, 640614400, 10109696000, 12652134400, 160153600, 12812288000, 320307200] }
def cert_2166 : Certificate := {
  mu := [(⟨5, by omega⟩, -640614400), (⟨6, by omega⟩, -12171673600), (⟨9, by omega⟩, -640614400), (⟨21, by omega⟩, -640614400), (⟨34, by omega⟩, -78643200), (⟨37, by omega⟩, -640614400), (⟨42, by omega⟩, -640614400), (⟨46, by omega⟩, -52428800), (⟨50, by omega⟩, -640614400), (⟨62, by omega⟩, -640614400), (⟨74, by omega⟩, -640614400), (⟨82, by omega⟩, -640614400), (⟨89, by omega⟩, -24343347200)]
  nu := [(⟨0, by omega⟩, -12171673600), (⟨3, by omega⟩, 12171673600), (⟨4, by omega⟩, 12171673600), (⟨5, by omega⟩, -640614400), (⟨10, by omega⟩, -12171673600), (⟨12, by omega⟩, 12171673600), (⟨16, by omega⟩, -640614400), (⟨20, by omega⟩, -12171673600), (⟨21, by omega⟩, 12171673600), (⟨22, by omega⟩, 78643200), (⟨23, by omega⟩, 52428800), (⟨25, by omega⟩, -78643200), (⟨26, by omega⟩, -52428800), (⟨28, by omega⟩, -640614400), (⟨30, by omega⟩, -13452902400), (⟨31, by omega⟩, 1281228800), (⟨32, by omega⟩, 1281228800), (⟨33, by omega⟩, 12812288000), (⟨34, by omega⟩, 12812288000), (⟨35, by omega⟩, -640614400), (⟨36, by omega⟩, -640614400), (⟨37, by omega⟩, -640614400), (⟨38, by omega⟩, -640614400), (⟨39, by omega⟩, -640614400), (⟨40, by omega⟩, -12171673600)]
  claimed := 1105348372945070291156992000000
}
def branch_box_2166 : RatBox 8 := { lower := box_2166.profileLo, upper := box_2166.profileHi }
def accepted_2166 : Bool := checkAt 527 1000 box_2166 cert_2166

def box_2170 : Box := { S := 101056512000, lo := ![0, 70621132800, 0, 78437222400, 98530099200, 0, 99793305600, 0], hi := ![2526412800, 71055360000, 5052825600, 78871449600, 99793305600, 1263206400, 101056512000, 2526412800] }
def cert_2170 : Certificate := {
  mu := [(⟨5, by omega⟩, -5052825600), (⟨6, by omega⟩, -96003686400), (⟨9, by omega⟩, -5052825600), (⟨21, by omega⟩, -5052825600), (⟨34, by omega⟩, -629145600), (⟨37, by omega⟩, -5052825600), (⟨42, by omega⟩, -5052825600), (⟨46, by omega⟩, -419430400), (⟨50, by omega⟩, -5052825600), (⟨62, by omega⟩, -5052825600), (⟨74, by omega⟩, -5052825600), (⟨82, by omega⟩, -5052825600), (⟨89, by omega⟩, -192007372800)]
  nu := [(⟨0, by omega⟩, -96003686400), (⟨3, by omega⟩, 96003686400), (⟨4, by omega⟩, 96003686400), (⟨5, by omega⟩, -5052825600), (⟨10, by omega⟩, -96003686400), (⟨12, by omega⟩, 96003686400), (⟨16, by omega⟩, -5052825600), (⟨20, by omega⟩, -96003686400), (⟨21, by omega⟩, 96003686400), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -5052825600), (⟨30, by omega⟩, -106109337600), (⟨31, by omega⟩, 10105651200), (⟨32, by omega⟩, 10105651200), (⟨33, by omega⟩, 101056512000), (⟨34, by omega⟩, 101056512000), (⟨35, by omega⟩, -5052825600), (⟨36, by omega⟩, -5052825600), (⟨37, by omega⟩, -5052825600), (⟨38, by omega⟩, -5052825600), (⟨39, by omega⟩, -5052825600), (⟨40, by omega⟩, -96003686400)]
  claimed := 542408524401588941340278784000000
}
def branch_box_2170 : RatBox 8 := { lower := box_2170.profileLo, upper := box_2170.profileHi }
def accepted_2170 : Bool := checkAt 527 1000 box_2170 cert_2170

def box_2178 : Box := { S := 10150400, lo := ![0, 7006155, 0, 7965685, 10023520, 0, 9896640, 0], hi := ![253760, 7049770, 507520, 8009300, 10150400, 126880, 10150400, 253760] }
def cert_2178 : Certificate := {
  mu := [(⟨4, by omega⟩, -253760), (⟨6, by omega⟩, -10150400), (⟨54, by omega⟩, -819200), (⟨90, by omega⟩, -20300800)]
  nu := [(⟨0, by omega⟩, -10150400), (⟨3, by omega⟩, 10150400), (⟨4, by omega⟩, 10150400), (⟨10, by omega⟩, -10150400), (⟨12, by omega⟩, 10150400), (⟨20, by omega⟩, -10150400), (⟨21, by omega⟩, 10150400), (⟨24, by omega⟩, 819200), (⟨27, by omega⟩, -819200), (⟨30, by omega⟩, -10150400), (⟨33, by omega⟩, 10150400), (⟨34, by omega⟩, 10150400), (⟨40, by omega⟩, -10150400)]
  claimed := 549372866734981120000
}
def branch_box_2178 : RatBox 8 := { lower := box_2178.profileLo, upper := box_2178.profileHi }
def accepted_2178 : Bool := checkAt 527 1000 box_2178 cert_2178

def box_2180 : Box := { S := 2502400, lo := ![0, 1737995, 0, 1953045, 2471120, 0, 2439840, 0], hi := ![62560, 1759500, 125120, 1974550, 2502400, 31280, 2502400, 62560] }
def cert_2180 : Certificate := {
  mu := [(⟨4, by omega⟩, -62560), (⟨6, by omega⟩, -2502400), (⟨54, by omega⟩, -204800), (⟨90, by omega⟩, -5004800)]
  nu := [(⟨0, by omega⟩, -2502400), (⟨3, by omega⟩, 2502400), (⟨4, by omega⟩, 2502400), (⟨10, by omega⟩, -2502400), (⟨12, by omega⟩, 2502400), (⟨20, by omega⟩, -2502400), (⟨21, by omega⟩, 2502400), (⟨24, by omega⟩, 204800), (⟨27, by omega⟩, -204800), (⟨30, by omega⟩, -2502400), (⟨33, by omega⟩, 2502400), (⟨34, by omega⟩, 2502400), (⟨40, by omega⟩, -2502400)]
  claimed := 8231669575761920000
}
def branch_box_2180 : RatBox 8 := { lower := box_2180.profileLo, upper := box_2180.profileHi }
def accepted_2180 : Bool := checkAt 527 1000 box_2180 cert_2180

def box_2184 : Box := { S := 9868800, lo := ![0, 6896595, 0, 7659885, 9745440, 0, 9622080, 0], hi := ![246720, 6939000, 493440, 7702290, 9868800, 123360, 9868800, 246720] }
def cert_2184 : Certificate := {
  mu := [(⟨4, by omega⟩, -246720), (⟨6, by omega⟩, -9868800), (⟨54, by omega⟩, -819200), (⟨90, by omega⟩, -19737600)]
  nu := [(⟨0, by omega⟩, -9868800), (⟨3, by omega⟩, 9868800), (⟨4, by omega⟩, 9868800), (⟨10, by omega⟩, -9868800), (⟨12, by omega⟩, 9868800), (⟨20, by omega⟩, -9868800), (⟨21, by omega⟩, 9868800), (⟨24, by omega⟩, 819200), (⟨27, by omega⟩, -819200), (⟨30, by omega⟩, -9868800), (⟨33, by omega⟩, 9868800), (⟨34, by omega⟩, 9868800), (⟨40, by omega⟩, -9868800)]
  claimed := 504906286688501760000
}
def branch_box_2184 : RatBox 8 := { lower := box_2184.profileLo, upper := box_2184.profileHi }
def accepted_2184 : Bool := checkAt 527 1000 box_2184 cert_2184

def box_2189 : Box := { S := 7052800, lo := ![0, 4837780, 0, 5443880, 6876480, 88160, 6876480, 0], hi := ![176320, 4959000, 352640, 5565100, 6964640, 176320, 6964640, 88160] }
def cert_2189 : Certificate := {
  mu := [(⟨4, by omega⟩, -1582180), (⟨5, by omega⟩, -3993600), (⟨6, by omega⟩, -3059200), (⟨9, by omega⟩, -3993600), (⟨13, by omega⟩, -3059200), (⟨21, by omega⟩, -3059200), (⟨30, by omega⟩, -3059200), (⟨33, by omega⟩, -3059200), (⟨37, by omega⟩, -3993600), (⟨42, by omega⟩, -3993600), (⟨45, by omega⟩, -3059200), (⟨50, by omega⟩, -3993600), (⟨54, by omega⟩, -3059200), (⟨61, by omega⟩, -3059200), (⟨70, by omega⟩, -3059200), (⟨74, by omega⟩, -3993600), (⟨77, by omega⟩, -3059200), (⟨82, by omega⟩, -3993600), (⟨86, by omega⟩, -3059200), (⟨90, by omega⟩, -7987200), (⟨94, by omega⟩, -6118400)]
  nu := [(⟨0, by omega⟩, -3993600), (⟨3, by omega⟩, 3993600), (⟨4, by omega⟩, 3993600), (⟨5, by omega⟩, -3993600), (⟨10, by omega⟩, -3059200), (⟨11, by omega⟩, 3059200), (⟨12, by omega⟩, 3059200), (⟨13, by omega⟩, 3059200), (⟨14, by omega⟩, 3059200), (⟨15, by omega⟩, -3059200), (⟨16, by omega⟩, -3059200), (⟨17, by omega⟩, -3059200), (⟨18, by omega⟩, -3059200), (⟨19, by omega⟩, -3059200), (⟨20, by omega⟩, -3059200), (⟨21, by omega⟩, 3059200), (⟨22, by omega⟩, 3059200), (⟨23, by omega⟩, 3059200), (⟨24, by omega⟩, 3059200), (⟨25, by omega⟩, -3059200), (⟨26, by omega⟩, -3059200), (⟨27, by omega⟩, -3059200), (⟨28, by omega⟩, -3059200), (⟨29, by omega⟩, -3059200), (⟨30, by omega⟩, -11980800), (⟨31, by omega⟩, 7987200), (⟨32, by omega⟩, 7987200), (⟨33, by omega⟩, 7987200), (⟨34, by omega⟩, 7987200), (⟨35, by omega⟩, -3993600), (⟨36, by omega⟩, -3993600), (⟨37, by omega⟩, -3993600), (⟨38, by omega⟩, -3993600), (⟨39, by omega⟩, -3993600), (⟨40, by omega⟩, -3993600), (⟨41, by omega⟩, -3059200)]
  claimed := 183455066838302720000
}
def branch_box_2189 : RatBox 8 := { lower := box_2189.profileLo, upper := box_2189.profileHi }
def accepted_2189 : Bool := checkAt 527 1000 box_2189 cert_2189

def box_2196 : Box := { S := 259891200, lo := ![0, 179385840, 0, 202836960, 253393920, 3248640, 256642560, 0], hi := ![6497280, 180502560, 12994560, 205070400, 256642560, 6497280, 259891200, 3248640] }
def cert_2196 : Certificate := {
  mu := [(⟨5, by omega⟩, -13107200), (⟨6, by omega⟩, -246784000), (⟨9, by omega⟩, -13107200), (⟨13, by omega⟩, -246784000), (⟨21, by omega⟩, -246784000), (⟨34, by omega⟩, -246784000), (⟨37, by omega⟩, -13107200), (⟨42, by omega⟩, -13107200), (⟨45, by omega⟩, -246784000), (⟨50, by omega⟩, -13107200), (⟨61, by omega⟩, -246784000), (⟨74, by omega⟩, -13107200), (⟨77, by omega⟩, -246784000), (⟨82, by omega⟩, -13107200), (⟨89, by omega⟩, -493568000)]
  nu := [(⟨0, by omega⟩, -246784000), (⟨3, by omega⟩, 246784000), (⟨4, by omega⟩, 246784000), (⟨5, by omega⟩, -13107200), (⟨10, by omega⟩, -246784000), (⟨11, by omega⟩, 246784000), (⟨12, by omega⟩, 246784000), (⟨13, by omega⟩, 246784000), (⟨15, by omega⟩, -246784000), (⟨16, by omega⟩, -246784000), (⟨18, by omega⟩, -246784000), (⟨20, by omega⟩, -246784000), (⟨21, by omega⟩, 246784000), (⟨22, by omega⟩, 246784000), (⟨23, by omega⟩, 246784000), (⟨25, by omega⟩, -246784000), (⟨26, by omega⟩, -246784000), (⟨28, by omega⟩, -246784000), (⟨30, by omega⟩, -272998400), (⟨31, by omega⟩, 26214400), (⟨32, by omega⟩, 26214400), (⟨33, by omega⟩, 259891200), (⟨34, by omega⟩, 259891200), (⟨35, by omega⟩, -13107200), (⟨36, by omega⟩, -13107200), (⟨37, by omega⟩, -13107200), (⟨38, by omega⟩, -13107200), (⟨39, by omega⟩, -13107200), (⟨40, by omega⟩, -246784000)]
  claimed := 9184086100231355105280000
}
def branch_box_2196 : RatBox 8 := { lower := box_2196.profileLo, upper := box_2196.profileHi }
def accepted_2196 : Bool := checkAt 527 1000 box_2196 cert_2196

def box_2198 : Box := { S := 6400, lo := ![0, 4445, 0, 4995, 6240, 80, 6320, 0], hi := ![160, 4500, 320, 5050, 6320, 160, 6400, 80] }
def cert_2198 : Certificate := {
  mu := [(⟨6, by omega⟩, -6400), (⟨45, by omega⟩, -6400), (⟨77, by omega⟩, -6400), (⟨89, by omega⟩, -12800)]
  nu := [(⟨0, by omega⟩, -6400), (⟨3, by omega⟩, 6400), (⟨4, by omega⟩, 6400), (⟨10, by omega⟩, -6400), (⟨12, by omega⟩, 6400), (⟨13, by omega⟩, 6400), (⟨18, by omega⟩, -6400), (⟨20, by omega⟩, -6400), (⟨21, by omega⟩, 6400), (⟨23, by omega⟩, 6400), (⟨26, by omega⟩, -6400), (⟨30, by omega⟩, -6400), (⟨33, by omega⟩, 6400), (⟨34, by omega⟩, 6400), (⟨40, by omega⟩, -6400)]
  claimed := 136069120000
}
def branch_box_2198 : RatBox 8 := { lower := box_2198.profileLo, upper := box_2198.profileHi }
def accepted_2198 : Bool := checkAt 527 1000 box_2198 cert_2198

end PeaceableQueens.UpperBound.Generated.Even.Core
