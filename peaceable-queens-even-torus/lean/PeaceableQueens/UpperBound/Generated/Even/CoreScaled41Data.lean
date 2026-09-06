import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_2051 : Box := { S := 1195255040, lo := ![0, 799326808, 0, 953402653, 1165373664, 0, 1165373664, 0], hi := ![29881376, 809598531, 59762752, 963674376, 1172844008, 14940688, 1180314352, 29881376] }
def cert_2051 : Certificate := {
  mu := [(⟨5, by omega⟩, -676659200), (⟨6, by omega⟩, -518595840), (⟨9, by omega⟩, -676659200), (⟨21, by omega⟩, -676659200), (⟨33, by omega⟩, -518595840), (⟨37, by omega⟩, -676659200), (⟨42, by omega⟩, -676659200), (⟨45, by omega⟩, -52428800), (⟨50, by omega⟩, -676659200), (⟨62, by omega⟩, -676659200), (⟨74, by omega⟩, -676659200), (⟨82, by omega⟩, -676659200), (⟨89, by omega⟩, -1353318400)]
  nu := [(⟨0, by omega⟩, -676659200), (⟨3, by omega⟩, 676659200), (⟨4, by omega⟩, 676659200), (⟨5, by omega⟩, -676659200), (⟨10, by omega⟩, -518595840), (⟨12, by omega⟩, 518595840), (⟨16, by omega⟩, -676659200), (⟨20, by omega⟩, -518595840), (⟨21, by omega⟩, 518595840), (⟨22, by omega⟩, 518595840), (⟨23, by omega⟩, 52428800), (⟨25, by omega⟩, -518595840), (⟨26, by omega⟩, -52428800), (⟨28, by omega⟩, -676659200), (⟨30, by omega⟩, -2029977600), (⟨31, by omega⟩, 1353318400), (⟨32, by omega⟩, 1353318400), (⟨33, by omega⟩, 1353318400), (⟨34, by omega⟩, 1353318400), (⟨35, by omega⟩, -676659200), (⟨36, by omega⟩, -676659200), (⟨37, by omega⟩, -676659200), (⟨38, by omega⟩, -676659200), (⟨39, by omega⟩, -676659200), (⟨40, by omega⟩, -676659200)]
  claimed := 897363016324309649029529600
}
def branch_box_2051 : RatBox 8 := { lower := box_2051.profileLo, upper := box_2051.profileHi }
def accepted_2051 : Bool := checkAt 527 1000 box_2051 cert_2051

def box_2053 : Box := { S := 564345600, lo := ![0, 377406120, 0, 450153795, 553764120, 0, 550236960, 0], hi := ![14108640, 382255965, 28217280, 455003640, 557291280, 7054320, 553764120, 14108640] }
def cert_2053 : Certificate := {
  mu := [(⟨4, by omega⟩, -128550240), (⟨5, by omega⟩, -319488000), (⟨6, by omega⟩, -244857600), (⟨9, by omega⟩, -319488000), (⟨21, by omega⟩, -74630400), (⟨33, by omega⟩, -244857600), (⟨37, by omega⟩, -319488000), (⟨42, by omega⟩, -319488000), (⟨45, by omega⟩, -244857600), (⟨50, by omega⟩, -319488000), (⟨53, by omega⟩, -244857600), (⟨62, by omega⟩, -244857600), (⟨70, by omega⟩, -244857600), (⟨74, by omega⟩, -319488000), (⟨82, by omega⟩, -319488000), (⟨86, by omega⟩, -244857600), (⟨89, by omega⟩, -634374400), (⟨94, by omega⟩, -489715200)]
  nu := [(⟨0, by omega⟩, -319488000), (⟨3, by omega⟩, 319488000), (⟨4, by omega⟩, 319488000), (⟨5, by omega⟩, -319488000), (⟨10, by omega⟩, -244857600), (⟨12, by omega⟩, 244857600), (⟨14, by omega⟩, 244857600), (⟨16, by omega⟩, -74630400), (⟨19, by omega⟩, -244857600), (⟨20, by omega⟩, -244857600), (⟨21, by omega⟩, 244857600), (⟨22, by omega⟩, 244857600), (⟨23, by omega⟩, 244857600), (⟨24, by omega⟩, 244857600), (⟨25, by omega⟩, -244857600), (⟨26, by omega⟩, -244857600), (⟨27, by omega⟩, -244857600), (⟨28, by omega⟩, -244857600), (⟨29, by omega⟩, -244857600), (⟨30, by omega⟩, -958464000), (⟨31, by omega⟩, 638976000), (⟨32, by omega⟩, 638976000), (⟨33, by omega⟩, 638976000), (⟨34, by omega⟩, 638976000), (⟨35, by omega⟩, -319488000), (⟨36, by omega⟩, -319488000), (⟨37, by omega⟩, -319488000), (⟨38, by omega⟩, -319488000), (⟨39, by omega⟩, -319488000), (⟨40, by omega⟩, -319488000), (⟨41, by omega⟩, -244857600)]
  claimed := 94198440314572249743360000
}
def branch_box_2053 : RatBox 8 := { lower := box_2053.profileLo, upper := box_2053.profileHi }
def accepted_2053 : Bool := checkAt 527 1000 box_2053 cert_2053

def box_2058 : Box := { S := 444314419200, lo := ![0, 299044431360, 0, 356319336960, 435983523840, 0, 435983523840, 0], hi := ![11107860480, 300953594880, 22215720960, 358228500480, 438760488960, 5553930240, 438760488960, 11107860480] }
def cert_2058 : Certificate := {
  mu := [(⟨5, by omega⟩, -27426816000), (⟨6, by omega⟩, -416887603200), (⟨9, by omega⟩, -27426816000), (⟨21, by omega⟩, -27426816000), (⟨34, by omega⟩, -442217267200), (⟨37, by omega⟩, -27426816000), (⟨42, by omega⟩, -27426816000), (⟨46, by omega⟩, -2097152000), (⟨50, by omega⟩, -27426816000), (⟨62, by omega⟩, -2097152000), (⟨74, by omega⟩, -27426816000), (⟨82, by omega⟩, -27426816000), (⟨89, by omega⟩, -416887603200), (⟨90, by omega⟩, -416887603200)]
  nu := [(⟨0, by omega⟩, -416887603200), (⟨3, by omega⟩, 416887603200), (⟨4, by omega⟩, 416887603200), (⟨5, by omega⟩, -27426816000), (⟨10, by omega⟩, -416887603200), (⟨12, by omega⟩, 416887603200), (⟨16, by omega⟩, -27426816000), (⟨20, by omega⟩, -416887603200), (⟨21, by omega⟩, 416887603200), (⟨22, by omega⟩, 416887603200), (⟨23, by omega⟩, 2097152000), (⟨25, by omega⟩, -442217267200), (⟨26, by omega⟩, -2097152000), (⟨28, by omega⟩, -2097152000), (⟨30, by omega⟩, -471741235200), (⟨31, by omega⟩, 54853632000), (⟨32, by omega⟩, 54853632000), (⟨33, by omega⟩, 444314419200), (⟨34, by omega⟩, 444314419200), (⟨35, by omega⟩, -27426816000), (⟨36, by omega⟩, -27426816000), (⟨37, by omega⟩, -27426816000), (⟨38, by omega⟩, -27426816000), (⟨39, by omega⟩, -27426816000), (⟨40, by omega⟩, -416887603200)]
  claimed := 46091390943549796436194193571840000
}
def branch_box_2058 : RatBox 8 := { lower := box_2058.profileLo, upper := box_2058.profileHi }
def accepted_2058 : Bool := checkAt 527 1000 box_2058 cert_2058

def box_2060 : Box := { S := 67174400, lo := ![0, 45500160, 0, 53582080, 65495040, 0, 65495040, 0], hi := ![1679360, 46077440, 3358720, 54159360, 66334720, 839680, 66334720, 1679360] }
def cert_2060 : Certificate := {
  mu := [(⟨5, by omega⟩, -4915200), (⟨6, by omega⟩, -62259200), (⟨9, by omega⟩, -4915200), (⟨21, by omega⟩, -4915200), (⟨34, by omega⟩, -62259200), (⟨37, by omega⟩, -4915200), (⟨42, by omega⟩, -4915200), (⟨46, by omega⟩, -4915200), (⟨50, by omega⟩, -4915200), (⟨62, by omega⟩, -4915200), (⟨74, by omega⟩, -4915200), (⟨82, by omega⟩, -4915200), (⟨89, by omega⟩, -62259200), (⟨90, by omega⟩, -62259200)]
  nu := [(⟨0, by omega⟩, -62259200), (⟨3, by omega⟩, 62259200), (⟨4, by omega⟩, 62259200), (⟨5, by omega⟩, -4915200), (⟨10, by omega⟩, -62259200), (⟨12, by omega⟩, 62259200), (⟨16, by omega⟩, -4915200), (⟨20, by omega⟩, -62259200), (⟨21, by omega⟩, 62259200), (⟨22, by omega⟩, 62259200), (⟨23, by omega⟩, 4915200), (⟨25, by omega⟩, -62259200), (⟨26, by omega⟩, -4915200), (⟨28, by omega⟩, -4915200), (⟨30, by omega⟩, -72089600), (⟨31, by omega⟩, 9830400), (⟨32, by omega⟩, 9830400), (⟨33, by omega⟩, 67174400), (⟨34, by omega⟩, 67174400), (⟨35, by omega⟩, -4915200), (⟨36, by omega⟩, -4915200), (⟨37, by omega⟩, -4915200), (⟨38, by omega⟩, -4915200), (⟨39, by omega⟩, -4915200), (⟨40, by omega⟩, -62259200)]
  claimed := 159300305625850839040000
}
def branch_box_2060 : RatBox 8 := { lower := box_2060.profileLo, upper := box_2060.profileHi }
def accepted_2060 : Bool := checkAt 527 1000 box_2060 cert_2060

def box_2061 : Box := { S := 289440000, lo := ![0, 196050375, 0, 228386250, 282204000, 0, 282204000, 0], hi := ![7236000, 198537750, 14472000, 230873625, 284013000, 3618000, 285822000, 7236000] }
def cert_2061 : Certificate := {
  mu := [(⟨5, by omega⟩, -164659200), (⟨6, by omega⟩, -124780800), (⟨9, by omega⟩, -164659200), (⟨21, by omega⟩, -164659200), (⟨33, by omega⟩, -124780800), (⟨37, by omega⟩, -164659200), (⟨42, by omega⟩, -164659200), (⟨45, by omega⟩, -13107200), (⟨50, by omega⟩, -164659200), (⟨62, by omega⟩, -164659200), (⟨74, by omega⟩, -164659200), (⟨82, by omega⟩, -164659200), (⟨89, by omega⟩, -329318400)]
  nu := [(⟨0, by omega⟩, -164659200), (⟨3, by omega⟩, 164659200), (⟨4, by omega⟩, 164659200), (⟨5, by omega⟩, -164659200), (⟨10, by omega⟩, -124780800), (⟨12, by omega⟩, 124780800), (⟨16, by omega⟩, -164659200), (⟨20, by omega⟩, -124780800), (⟨21, by omega⟩, 124780800), (⟨22, by omega⟩, 124780800), (⟨23, by omega⟩, 13107200), (⟨25, by omega⟩, -124780800), (⟨26, by omega⟩, -13107200), (⟨28, by omega⟩, -164659200), (⟨30, by omega⟩, -493977600), (⟨31, by omega⟩, 329318400), (⟨32, by omega⟩, 329318400), (⟨33, by omega⟩, 329318400), (⟨34, by omega⟩, 329318400), (⟨35, by omega⟩, -164659200), (⟨36, by omega⟩, -164659200), (⟨37, by omega⟩, -164659200), (⟨38, by omega⟩, -164659200), (⟨39, by omega⟩, -164659200), (⟨40, by omega⟩, -164659200)]
  claimed := 12756022783811942400000000
}
def branch_box_2061 : RatBox 8 := { lower := box_2061.profileLo, upper := box_2061.profileHi }
def accepted_2061 : Bool := checkAt 527 1000 box_2061 cert_2061

def box_2063 : Box := { S := 1440000, lo := ![0, 975375, 0, 1136250, 1413000, 0, 1404000, 0], hi := ![36000, 987750, 72000, 1148625, 1422000, 18000, 1413000, 36000] }
def cert_2063 : Certificate := {
  mu := [(⟨4, by omega⟩, -325920), (⟨5, by omega⟩, -819200), (⟨6, by omega⟩, -620800), (⟨9, by omega⟩, -819200), (⟨21, by omega⟩, -819200), (⟨33, by omega⟩, -620800), (⟨37, by omega⟩, -819200), (⟨42, by omega⟩, -819200), (⟨50, by omega⟩, -819200), (⟨53, by omega⟩, -620800), (⟨62, by omega⟩, -198400), (⟨70, by omega⟩, -620800), (⟨74, by omega⟩, -819200), (⟨82, by omega⟩, -819200), (⟨86, by omega⟩, -620800), (⟨89, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -819200), (⟨3, by omega⟩, 819200), (⟨4, by omega⟩, 819200), (⟨5, by omega⟩, -819200), (⟨10, by omega⟩, -620800), (⟨12, by omega⟩, 620800), (⟨14, by omega⟩, 620800), (⟨16, by omega⟩, -819200), (⟨19, by omega⟩, -620800), (⟨20, by omega⟩, -620800), (⟨21, by omega⟩, 620800), (⟨22, by omega⟩, 620800), (⟨24, by omega⟩, 620800), (⟨25, by omega⟩, -620800), (⟨27, by omega⟩, -620800), (⟨28, by omega⟩, -198400), (⟨29, by omega⟩, -620800), (⟨30, by omega⟩, -2457600), (⟨31, by omega⟩, 1638400), (⟨32, by omega⟩, 1638400), (⟨33, by omega⟩, 1638400), (⟨34, by omega⟩, 1638400), (⟨35, by omega⟩, -819200), (⟨36, by omega⟩, -819200), (⟨37, by omega⟩, -819200), (⟨38, by omega⟩, -819200), (⟨39, by omega⟩, -819200), (⟨40, by omega⟩, -819200)]
  claimed := 1566598579200000000
}
def branch_box_2063 : RatBox 8 := { lower := box_2063.profileLo, upper := box_2063.profileHi }
def accepted_2063 : Bool := checkAt 527 1000 box_2063 cert_2063

def box_2068 : Box := { S := 530841600, lo := ![0, 361843200, 0, 421148160, 520888320, 0, 520888320, 0], hi := ![13271040, 364124160, 26542080, 423429120, 524206080, 6635520, 524206080, 13271040] }
def cert_2068 : Certificate := {
  mu := [(⟨5, by omega⟩, -32768000), (⟨6, by omega⟩, -498073600), (⟨9, by omega⟩, -32768000), (⟨21, by omega⟩, -32768000), (⟨34, by omega⟩, -498073600), (⟨37, by omega⟩, -32768000), (⟨42, by omega⟩, -32768000), (⟨46, by omega⟩, -498073600), (⟨50, by omega⟩, -32768000), (⟨62, by omega⟩, -498073600), (⟨74, by omega⟩, -32768000), (⟨82, by omega⟩, -32768000), (⟨89, by omega⟩, -498073600), (⟨90, by omega⟩, -498073600)]
  nu := [(⟨0, by omega⟩, -498073600), (⟨3, by omega⟩, 498073600), (⟨4, by omega⟩, 498073600), (⟨5, by omega⟩, -32768000), (⟨10, by omega⟩, -498073600), (⟨12, by omega⟩, 498073600), (⟨16, by omega⟩, -32768000), (⟨20, by omega⟩, -498073600), (⟨21, by omega⟩, 498073600), (⟨22, by omega⟩, 498073600), (⟨23, by omega⟩, 498073600), (⟨25, by omega⟩, -498073600), (⟨26, by omega⟩, -498073600), (⟨28, by omega⟩, -498073600), (⟨30, by omega⟩, -563609600), (⟨31, by omega⟩, 65536000), (⟨32, by omega⟩, 65536000), (⟨33, by omega⟩, 530841600), (⟨34, by omega⟩, 530841600), (⟨35, by omega⟩, -32768000), (⟨36, by omega⟩, -32768000), (⟨37, by omega⟩, -32768000), (⟨38, by omega⟩, -32768000), (⟨39, by omega⟩, -32768000), (⟨40, by omega⟩, -498073600)]
  claimed := 78613328769732134830080000
}
def branch_box_2068 : RatBox 8 := { lower := box_2068.profileLo, upper := box_2068.profileHi }
def accepted_2068 : Bool := checkAt 527 1000 box_2068 cert_2068

def box_2076 : Box := { S := 6180175872000, lo := ![0, 4159548057600, 0, 4956211353600, 6025671475200, 0, 6102923673600, 0], hi := ![154504396800, 4186103500800, 309008793600, 4982766796800, 6102923673600, 77252198400, 6180175872000, 154504396800] }
def cert_2076 : Certificate := {
  mu := [(⟨5, by omega⟩, -309008793600), (⟨6, by omega⟩, -5871167078400), (⟨9, by omega⟩, -309008793600), (⟨13, by omega⟩, -19503513600), (⟨22, by omega⟩, -309008793600), (⟨34, by omega⟩, -35441868800), (⟨37, by omega⟩, -309008793600), (⟨42, by omega⟩, -309008793600), (⟨50, by omega⟩, -309008793600), (⟨62, by omega⟩, -309008793600), (⟨74, by omega⟩, -309008793600), (⟨82, by omega⟩, -309008793600), (⟨89, by omega⟩, -11742334156800)]
  nu := [(⟨0, by omega⟩, -5871167078400), (⟨3, by omega⟩, 5871167078400), (⟨4, by omega⟩, 5871167078400), (⟨5, by omega⟩, -309008793600), (⟨10, by omega⟩, -5871167078400), (⟨11, by omega⟩, 19503513600), (⟨12, by omega⟩, 5871167078400), (⟨15, by omega⟩, -19503513600), (⟨16, by omega⟩, -309008793600), (⟨20, by omega⟩, -5871167078400), (⟨21, by omega⟩, 5871167078400), (⟨22, by omega⟩, 35441868800), (⟨25, by omega⟩, -35441868800), (⟨28, by omega⟩, -309008793600), (⟨30, by omega⟩, -6489184665600), (⟨31, by omega⟩, 618017587200), (⟨32, by omega⟩, 618017587200), (⟨33, by omega⟩, 6180175872000), (⟨34, by omega⟩, 6180175872000), (⟨35, by omega⟩, -309008793600), (⟨36, by omega⟩, -309008793600), (⟨37, by omega⟩, -309008793600), (⟨38, by omega⟩, -309008793600), (⟨39, by omega⟩, -309008793600), (⟨40, by omega⟩, -5871167078400)]
  claimed := 124029854638464393430890266492928000000
}
def branch_box_2076 : RatBox 8 := { lower := box_2076.profileLo, upper := box_2076.profileHi }
def accepted_2076 : Bool := checkAt 527 1000 box_2076 cert_2076

def box_2078 : Box := { S := 13533184000, lo := ![0, 9166617600, 0, 10794828800, 13194854400, 0, 13364019200, 0], hi := ![338329600, 9282918400, 676659200, 10911129600, 13364019200, 169164800, 13533184000, 338329600] }
def cert_2078 : Certificate := {
  mu := [(⟨5, by omega⟩, -676659200), (⟨6, by omega⟩, -12856524800), (⟨9, by omega⟩, -676659200), (⟨21, by omega⟩, -676659200), (⟨34, by omega⟩, -78643200), (⟨37, by omega⟩, -676659200), (⟨42, by omega⟩, -676659200), (⟨46, by omega⟩, -52428800), (⟨50, by omega⟩, -676659200), (⟨62, by omega⟩, -676659200), (⟨74, by omega⟩, -676659200), (⟨82, by omega⟩, -676659200), (⟨89, by omega⟩, -25713049600)]
  nu := [(⟨0, by omega⟩, -12856524800), (⟨3, by omega⟩, 12856524800), (⟨4, by omega⟩, 12856524800), (⟨5, by omega⟩, -676659200), (⟨10, by omega⟩, -12856524800), (⟨12, by omega⟩, 12856524800), (⟨16, by omega⟩, -676659200), (⟨20, by omega⟩, -12856524800), (⟨21, by omega⟩, 12856524800), (⟨22, by omega⟩, 78643200), (⟨23, by omega⟩, 52428800), (⟨25, by omega⟩, -78643200), (⟨26, by omega⟩, -52428800), (⟨28, by omega⟩, -676659200), (⟨30, by omega⟩, -14209843200), (⟨31, by omega⟩, 1353318400), (⟨32, by omega⟩, 1353318400), (⟨33, by omega⟩, 13533184000), (⟨34, by omega⟩, 13533184000), (⟨35, by omega⟩, -676659200), (⟨36, by omega⟩, -676659200), (⟨37, by omega⟩, -676659200), (⟨38, by omega⟩, -676659200), (⟨39, by omega⟩, -676659200), (⟨40, by omega⟩, -12856524800)]
  claimed := 1302404292948923129004032000000
}
def branch_box_2078 : RatBox 8 := { lower := box_2078.profileLo, upper := box_2078.profileHi }
def accepted_2078 : Bool := checkAt 527 1000 box_2078 cert_2078

def box_2082 : Box := { S := 21364736000, lo := ![0, 14563072000, 0, 16949913600, 20830617600, 0, 21097676800, 0], hi := ![534118400, 14654873600, 1068236800, 17041715200, 21097676800, 267059200, 21364736000, 534118400] }
def cert_2082 : Certificate := {
  mu := [(⟨5, by omega⟩, -1068236800), (⟨6, by omega⟩, -20296499200), (⟨9, by omega⟩, -1068236800), (⟨21, by omega⟩, -1068236800), (⟨34, by omega⟩, -125829120), (⟨37, by omega⟩, -1068236800), (⟨42, by omega⟩, -1068236800), (⟨46, by omega⟩, -83886080), (⟨50, by omega⟩, -1068236800), (⟨62, by omega⟩, -1068236800), (⟨74, by omega⟩, -1068236800), (⟨82, by omega⟩, -1068236800), (⟨89, by omega⟩, -40592998400)]
  nu := [(⟨0, by omega⟩, -20296499200), (⟨3, by omega⟩, 20296499200), (⟨4, by omega⟩, 20296499200), (⟨5, by omega⟩, -1068236800), (⟨10, by omega⟩, -20296499200), (⟨12, by omega⟩, 20296499200), (⟨16, by omega⟩, -1068236800), (⟨20, by omega⟩, -20296499200), (⟨21, by omega⟩, 20296499200), (⟨22, by omega⟩, 125829120), (⟨23, by omega⟩, 83886080), (⟨25, by omega⟩, -125829120), (⟨26, by omega⟩, -83886080), (⟨28, by omega⟩, -1068236800), (⟨30, by omega⟩, -22432972800), (⟨31, by omega⟩, 2136473600), (⟨32, by omega⟩, 2136473600), (⟨33, by omega⟩, 21364736000), (⟨34, by omega⟩, 21364736000), (⟨35, by omega⟩, -1068236800), (⟨36, by omega⟩, -1068236800), (⟨37, by omega⟩, -1068236800), (⟨38, by omega⟩, -1068236800), (⟨39, by omega⟩, -1068236800), (⟨40, by omega⟩, -20296499200)]
  claimed := 5124589132840520504049664000000
}
def branch_box_2082 : RatBox 8 := { lower := box_2082.profileLo, upper := box_2082.profileHi }
def accepted_2082 : Bool := checkAt 527 1000 box_2082 cert_2082

def box_2090 : Box := { S := 10713600, lo := ![0, 7210755, 0, 8591805, 10579680, 0, 10445760, 0], hi := ![267840, 7256790, 535680, 8637840, 10713600, 133920, 10713600, 267840] }
def cert_2090 : Certificate := {
  mu := [(⟨4, by omega⟩, -267840), (⟨6, by omega⟩, -10713600), (⟨13, by omega⟩, -10713600), (⟨34, by omega⟩, -9894400), (⟨54, by omega⟩, -819200), (⟨90, by omega⟩, -21427200)]
  nu := [(⟨0, by omega⟩, -10713600), (⟨3, by omega⟩, 10713600), (⟨4, by omega⟩, 10713600), (⟨10, by omega⟩, -10713600), (⟨11, by omega⟩, 10713600), (⟨12, by omega⟩, 10713600), (⟨15, by omega⟩, -10713600), (⟨20, by omega⟩, -10713600), (⟨21, by omega⟩, 10713600), (⟨22, by omega⟩, 9894400), (⟨24, by omega⟩, 819200), (⟨25, by omega⟩, -9894400), (⟨27, by omega⟩, -819200), (⟨30, by omega⟩, -10713600), (⟨33, by omega⟩, 10713600), (⟨34, by omega⟩, 10713600), (⟨40, by omega⟩, -10713600)]
  claimed := 645987356700180480000
}
def branch_box_2090 : RatBox 8 := { lower := box_2090.profileLo, upper := box_2090.profileHi }
def accepted_2090 : Bool := checkAt 527 1000 box_2090 cert_2090

def box_2092 : Box := { S := 2643200, lo := ![0, 1790355, 0, 2108365, 2610160, 0, 2577120, 0], hi := ![66080, 1813070, 132160, 2131080, 2643200, 33040, 2643200, 66080] }
def cert_2092 : Certificate := {
  mu := [(⟨4, by omega⟩, -66080), (⟨6, by omega⟩, -2643200), (⟨46, by omega⟩, -2643200), (⟨54, by omega⟩, -204800), (⟨90, by omega⟩, -5286400), (⟨94, by omega⟩, -409600)]
  nu := [(⟨0, by omega⟩, -2643200), (⟨3, by omega⟩, 2643200), (⟨4, by omega⟩, 2643200), (⟨10, by omega⟩, -2643200), (⟨12, by omega⟩, 2643200), (⟨20, by omega⟩, -2643200), (⟨21, by omega⟩, 2643200), (⟨23, by omega⟩, 2643200), (⟨24, by omega⟩, 204800), (⟨26, by omega⟩, -2643200), (⟨27, by omega⟩, -204800), (⟨30, by omega⟩, -2643200), (⟨33, by omega⟩, 2643200), (⟨34, by omega⟩, 2643200), (⟨40, by omega⟩, -2643200), (⟨41, by omega⟩, -204800)]
  claimed := 9700805833277440000
}
def branch_box_2092 : RatBox 8 := { lower := box_2092.profileLo, upper := box_2092.profileHi }
def accepted_2092 : Bool := checkAt 527 1000 box_2092 cert_2092

def box_2096 : Box := { S := 2086400, lo := ![0, 1422175, 0, 1655265, 2060320, 0, 2034240, 0], hi := ![52160, 1431140, 104320, 1664230, 2086400, 26080, 2086400, 52160] }
def cert_2096 : Certificate := {
  mu := [(⟨4, by omega⟩, -52160), (⟨6, by omega⟩, -2086400), (⟨54, by omega⟩, -163840), (⟨90, by omega⟩, -4172800)]
  nu := [(⟨0, by omega⟩, -2086400), (⟨3, by omega⟩, 2086400), (⟨4, by omega⟩, 2086400), (⟨10, by omega⟩, -2086400), (⟨12, by omega⟩, 2086400), (⟨20, by omega⟩, -2086400), (⟨21, by omega⟩, 2086400), (⟨24, by omega⟩, 163840), (⟨27, by omega⟩, -163840), (⟨30, by omega⟩, -2086400), (⟨33, by omega⟩, 2086400), (⟨34, by omega⟩, 2086400), (⟨40, by omega⟩, -2086400)]
  claimed := 4771011432939520000
}
def branch_box_2096 : RatBox 8 := { lower := box_2096.profileLo, upper := box_2096.profileHi }
def accepted_2096 : Bool := checkAt 527 1000 box_2096 cert_2096

end PeaceableQueens.UpperBound.Generated.Even.Core
