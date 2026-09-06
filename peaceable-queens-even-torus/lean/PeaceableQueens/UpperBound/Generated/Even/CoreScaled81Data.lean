import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_4052 : Box := { S := 1030553600, lo := ![0, 768889600, 0, 742320640, 1004789760, 12881920, 1017671680, 0], hi := ![25763840, 777745920, 51527680, 760033280, 1017671680, 25763840, 1030553600, 12881920] }
def cert_4052 : Certificate := {
  mu := [(⟨3, by omega⟩, -236125440), (⟨5, by omega⟩, -52428800), (⟨6, by omega⟩, -978124800), (⟨10, by omega⟩, -52428800), (⟨21, by omega⟩, -52428800), (⟨34, by omega⟩, -978124800), (⟨37, by omega⟩, -52428800), (⟨42, by omega⟩, -52428800), (⟨45, by omega⟩, -978124800), (⟨50, by omega⟩, -52428800), (⟨61, by omega⟩, -978124800), (⟨74, by omega⟩, -52428800), (⟨77, by omega⟩, -978124800), (⟨82, by omega⟩, -52428800), (⟨89, by omega⟩, -1956249600)]
  nu := [(⟨0, by omega⟩, -978124800), (⟨3, by omega⟩, 978124800), (⟨4, by omega⟩, 978124800), (⟨5, by omega⟩, -52428800), (⟨10, by omega⟩, -978124800), (⟨12, by omega⟩, 978124800), (⟨13, by omega⟩, 978124800), (⟨16, by omega⟩, -52428800), (⟨18, by omega⟩, -978124800), (⟨20, by omega⟩, -978124800), (⟨21, by omega⟩, 978124800), (⟨22, by omega⟩, 978124800), (⟨23, by omega⟩, 978124800), (⟨25, by omega⟩, -978124800), (⟨26, by omega⟩, -978124800), (⟨28, by omega⟩, -978124800), (⟨30, by omega⟩, -1082982400), (⟨31, by omega⟩, 104857600), (⟨32, by omega⟩, 104857600), (⟨33, by omega⟩, 1030553600), (⟨34, by omega⟩, 1030553600), (⟨35, by omega⟩, -52428800), (⟨36, by omega⟩, -52428800), (⟨37, by omega⟩, -52428800), (⟨38, by omega⟩, -52428800), (⟨39, by omega⟩, -52428800), (⟨40, by omega⟩, -978124800)]
  claimed := 570507365592689341890560000
}
def branch_box_4052 : RatBox 8 := { lower := box_4052.profileLo, upper := box_4052.profileHi }
def accepted_4052 : Bool := checkAt 527 1000 box_4052 cert_4052

def box_4054 : Box := { S := 64409600, lo := ![0, 47502080, 0, 46948560, 62799360, 805120, 63604480, 0], hi := ![1610240, 48055600, 3220480, 47502080, 63604480, 1610240, 64409600, 805120] }
def cert_4054 : Certificate := {
  mu := [(⟨3, by omega⟩, -15283200), (⟨5, by omega⟩, -3276800), (⟨6, by omega⟩, -61132800), (⟨10, by omega⟩, -3276800), (⟨13, by omega⟩, -61132800), (⟨21, by omega⟩, -61132800), (⟨34, by omega⟩, -61132800), (⟨37, by omega⟩, -3276800), (⟨42, by omega⟩, -3276800), (⟨45, by omega⟩, -61132800), (⟨50, by omega⟩, -3276800), (⟨61, by omega⟩, -61132800), (⟨74, by omega⟩, -3276800), (⟨77, by omega⟩, -61132800), (⟨82, by omega⟩, -3276800), (⟨89, by omega⟩, -122265600)]
  nu := [(⟨0, by omega⟩, -61132800), (⟨3, by omega⟩, 61132800), (⟨4, by omega⟩, 61132800), (⟨5, by omega⟩, -3276800), (⟨10, by omega⟩, -61132800), (⟨11, by omega⟩, 61132800), (⟨12, by omega⟩, 61132800), (⟨13, by omega⟩, 61132800), (⟨15, by omega⟩, -61132800), (⟨16, by omega⟩, -61132800), (⟨18, by omega⟩, -61132800), (⟨20, by omega⟩, -61132800), (⟨21, by omega⟩, 61132800), (⟨22, by omega⟩, 61132800), (⟨23, by omega⟩, 61132800), (⟨25, by omega⟩, -61132800), (⟨26, by omega⟩, -61132800), (⟨28, by omega⟩, -61132800), (⟨30, by omega⟩, -67686400), (⟨31, by omega⟩, 6553600), (⟨32, by omega⟩, 6553600), (⟨33, by omega⟩, 64409600), (⟨34, by omega⟩, 64409600), (⟨35, by omega⟩, -3276800), (⟨36, by omega⟩, -3276800), (⟨37, by omega⟩, -3276800), (⟨38, by omega⟩, -3276800), (⟨39, by omega⟩, -3276800), (⟨40, by omega⟩, -61132800)]
  claimed := 140319595664234250240000
}
def branch_box_4054 : RatBox 8 := { lower := box_4054.profileLo, upper := box_4054.profileHi }
def accepted_4054 : Bool := checkAt 527 1000 box_4054 cert_4054

def box_4056 : Box := { S := 515440640, lo := ![0, 384567040, 0, 371278336, 508997632, 6443008, 502554624, 0], hi := ![12886016, 388996608, 25772032, 380137472, 515440640, 12886016, 515440640, 6443008] }
def cert_4056 : Certificate := {
  mu := [(⟨3, by omega⟩, -124430592), (⟨4, by omega⟩, -236377856), (⟨6, by omega⟩, -515440640), (⟨34, by omega⟩, -515440640), (⟨45, by omega⟩, -515440640), (⟨50, by omega⟩, -181862400), (⟨54, by omega⟩, -515440640), (⟨61, by omega⟩, -515440640), (⟨69, by omega⟩, -515440640), (⟨77, by omega⟩, -515440640), (⟨86, by omega⟩, -515440640), (⟨90, by omega⟩, -667156480), (⟨94, by omega⟩, -1030881280)]
  nu := [(⟨0, by omega⟩, -515440640), (⟨3, by omega⟩, 333578240), (⟨4, by omega⟩, 515440640), (⟨10, by omega⟩, -515440640), (⟨12, by omega⟩, 515440640), (⟨13, by omega⟩, 515440640), (⟨14, by omega⟩, 515440640), (⟨18, by omega⟩, -515440640), (⟨19, by omega⟩, -515440640), (⟨20, by omega⟩, -515440640), (⟨21, by omega⟩, 515440640), (⟨22, by omega⟩, 515440640), (⟨23, by omega⟩, 515440640), (⟨24, by omega⟩, 515440640), (⟨25, by omega⟩, -515440640), (⟨26, by omega⟩, -515440640), (⟨27, by omega⟩, -515440640), (⟨28, by omega⟩, -515440640), (⟨29, by omega⟩, -515440640), (⟨30, by omega⟩, -515440640), (⟨31, by omega⟩, 181862400), (⟨33, by omega⟩, 333578240), (⟨34, by omega⟩, 515440640), (⟨37, by omega⟩, -181862400), (⟨40, by omega⟩, -333578240), (⟨41, by omega⟩, -515440640)]
  claimed := 71305595552999059908198400
}
def branch_box_4056 : RatBox 8 := { lower := box_4056.profileLo, upper := box_4056.profileHi }
def accepted_4056 : Bool := checkAt 527 1000 box_4056 cert_4056

def box_4058 : Box := { S := 102400, lo := ![0, 75520, 0, 74640, 101120, 1280, 99840, 0], hi := ![2560, 76400, 5120, 75520, 102400, 2560, 102400, 1280] }
def cert_4058 : Certificate := {
  mu := [(⟨3, by omega⟩, -25600), (⟨4, by omega⟩, -2560), (⟨6, by omega⟩, -102400), (⟨34, by omega⟩, -102400), (⟨45, by omega⟩, -102400), (⟨54, by omega⟩, -102400), (⟨61, by omega⟩, -102400), (⟨69, by omega⟩, -102400), (⟨77, by omega⟩, -102400), (⟨86, by omega⟩, -102400), (⟨90, by omega⟩, -204800), (⟨94, by omega⟩, -204800)]
  nu := [(⟨0, by omega⟩, -102400), (⟨3, by omega⟩, 102400), (⟨4, by omega⟩, 102400), (⟨10, by omega⟩, -102400), (⟨12, by omega⟩, 102400), (⟨13, by omega⟩, 102400), (⟨14, by omega⟩, 102400), (⟨18, by omega⟩, -102400), (⟨19, by omega⟩, -102400), (⟨20, by omega⟩, -102400), (⟨21, by omega⟩, 102400), (⟨22, by omega⟩, 102400), (⟨23, by omega⟩, 102400), (⟨24, by omega⟩, 102400), (⟨25, by omega⟩, -102400), (⟨26, by omega⟩, -102400), (⟨27, by omega⟩, -102400), (⟨28, by omega⟩, -102400), (⟨29, by omega⟩, -102400), (⟨30, by omega⟩, -102400), (⟨33, by omega⟩, 102400), (⟨34, by omega⟩, 102400), (⟨40, by omega⟩, -102400), (⟨41, by omega⟩, -102400)]
  claimed := 563473285120000
}
def branch_box_4058 : RatBox 8 := { lower := box_4058.profileLo, upper := box_4058.profileHi }
def accepted_4058 : Bool := checkAt 527 1000 box_4058 cert_4058

def box_4060 : Box := { S := 204800, lo := ![0, 154560, 0, 147520, 199680, 0, 199680, 0], hi := ![5120, 158080, 10240, 151040, 204800, 5120, 204800, 5120] }
def cert_4060 : Certificate := {
  mu := [(⟨3, by omega⟩, -50240), (⟨6, by omega⟩, -204800), (⟨34, by omega⟩, -204800), (⟨46, by omega⟩, -204800), (⟨54, by omega⟩, -204800), (⟨61, by omega⟩, -204800), (⟨69, by omega⟩, -204800), (⟨89, by omega⟩, -409600), (⟨93, by omega⟩, -409600)]
  nu := [(⟨0, by omega⟩, -204800), (⟨3, by omega⟩, 204800), (⟨4, by omega⟩, 204800), (⟨10, by omega⟩, -204800), (⟨12, by omega⟩, 204800), (⟨20, by omega⟩, -204800), (⟨21, by omega⟩, 204800), (⟨22, by omega⟩, 204800), (⟨23, by omega⟩, 204800), (⟨24, by omega⟩, 204800), (⟨25, by omega⟩, -204800), (⟨26, by omega⟩, -204800), (⟨27, by omega⟩, -204800), (⟨28, by omega⟩, -204800), (⟨29, by omega⟩, -204800), (⟨30, by omega⟩, -204800), (⟨33, by omega⟩, 204800), (⟨34, by omega⟩, 204800), (⟨40, by omega⟩, -204800), (⟨41, by omega⟩, -204800)]
  claimed := 4448017448960000
}
def branch_box_4060 : RatBox 8 := { lower := box_4060.profileLo, upper := box_4060.profileHi }
def accepted_4060 : Bool := checkAt 527 1000 box_4060 cert_4060

def box_4062 : Box := { S := 35596800, lo := ![0, 26864460, 0, 25029000, 34706880, 444960, 34706880, 0], hi := ![889920, 27476280, 1779840, 25640820, 35596800, 889920, 35596800, 889920] }
def cert_4062 : Certificate := {
  mu := [(⟨3, by omega⟩, -31940640), (⟨4, by omega⟩, -843840), (⟨5, by omega⟩, -1843200), (⟨6, by omega⟩, -33753600), (⟨10, by omega⟩, -1843200), (⟨34, by omega⟩, -33753600), (⟨38, by omega⟩, -1843200), (⟨42, by omega⟩, -1843200), (⟨45, by omega⟩, -33753600), (⟨50, by omega⟩, -1843200), (⟨54, by omega⟩, -1875200), (⟨61, by omega⟩, -33753600), (⟨69, by omega⟩, -1875200), (⟨74, by omega⟩, -1843200), (⟨77, by omega⟩, -33753600), (⟨82, by omega⟩, -1843200), (⟨85, by omega⟩, -1875200), (⟨90, by omega⟩, -67507200), (⟨94, by omega⟩, -3750400)]
  nu := [(⟨0, by omega⟩, -33753600), (⟨3, by omega⟩, 33753600), (⟨4, by omega⟩, 33753600), (⟨5, by omega⟩, -1843200), (⟨10, by omega⟩, -33753600), (⟨12, by omega⟩, 33753600), (⟨13, by omega⟩, 33753600), (⟨14, by omega⟩, 1875200), (⟨18, by omega⟩, -33753600), (⟨19, by omega⟩, -1875200), (⟨20, by omega⟩, -33753600), (⟨21, by omega⟩, 33753600), (⟨22, by omega⟩, 33753600), (⟨23, by omega⟩, 33753600), (⟨24, by omega⟩, 1875200), (⟨25, by omega⟩, -33753600), (⟨26, by omega⟩, -33753600), (⟨27, by omega⟩, -1875200), (⟨28, by omega⟩, -33753600), (⟨29, by omega⟩, -1875200), (⟨30, by omega⟩, -37440000), (⟨31, by omega⟩, 3686400), (⟨32, by omega⟩, 3686400), (⟨33, by omega⟩, 35596800), (⟨34, by omega⟩, 35596800), (⟨35, by omega⟩, -1843200), (⟨36, by omega⟩, -1843200), (⟨37, by omega⟩, -1843200), (⟨38, by omega⟩, -1843200), (⟨39, by omega⟩, -1843200), (⟨40, by omega⟩, -33753600), (⟨41, by omega⟩, -1875200)]
  claimed := 23564511042870804480000
}
def branch_box_4062 : RatBox 8 := { lower := box_4062.profileLo, upper := box_4062.profileHi }
def accepted_4062 : Bool := checkAt 527 1000 box_4062 cert_4062

def box_4065 : Box := { S := 1323397120000, lo := ![0, 998751264000, 0, 930513600000, 1290312192000, 0, 1290312192000, 0], hi := ![33084928000, 1021497152000, 66169856000, 953259488000, 1306854656000, 16542464000, 1306854656000, 33084928000] }
def cert_4065 : Certificate := {
  mu := [(⟨3, by omega⟩, -159589068160), (⟨5, by omega⟩, -672842956800), (⟨6, by omega⟩, -650554163200), (⟨10, by omega⟩, -348738969600), (⟨14, by omega⟩, -650554163200), (⟨21, by omega⟩, -672842956800), (⟨34, by omega⟩, -650554163200), (⟨38, by omega⟩, -672842956800), (⟨42, by omega⟩, -672842956800), (⟨50, by omega⟩, -672842956800), (⟨61, by omega⟩, -672842956800), (⟨74, by omega⟩, -672842956800), (⟨77, by omega⟩, -180427161600), (⟨82, by omega⟩, -672842956800), (⟨89, by omega⟩, -1345685913600)]
  nu := [(⟨0, by omega⟩, -672842956800), (⟨1, by omega⟩, -324103987200), (⟨3, by omega⟩, 672842956800), (⟨4, by omega⟩, 672842956800), (⟨5, by omega⟩, -348738969600), (⟨10, by omega⟩, -650554163200), (⟨11, by omega⟩, 650554163200), (⟨12, by omega⟩, 650554163200), (⟨13, by omega⟩, 180427161600), (⟨15, by omega⟩, -650554163200), (⟨16, by omega⟩, -672842956800), (⟨18, by omega⟩, -180427161600), (⟨20, by omega⟩, -650554163200), (⟨21, by omega⟩, 650554163200), (⟨22, by omega⟩, 650554163200), (⟨25, by omega⟩, -650554163200), (⟨28, by omega⟩, -672842956800), (⟨30, by omega⟩, -2018528870400), (⟨31, by omega⟩, 1345685913600), (⟨32, by omega⟩, 1345685913600), (⟨33, by omega⟩, 1345685913600), (⟨34, by omega⟩, 1345685913600), (⟨35, by omega⟩, -672842956800), (⟨36, by omega⟩, -672842956800), (⟨37, by omega⟩, -672842956800), (⟨38, by omega⟩, -672842956800), (⟨39, by omega⟩, -672842956800), (⟨40, by omega⟩, -672842956800)]
  claimed := 1215527800991048939269731123200000000
}
def branch_box_4065 : RatBox 8 := { lower := box_4065.profileLo, upper := box_4065.profileHi }
def accepted_4065 : Bool := checkAt 527 1000 box_4065 cert_4065

def box_4068 : Box := { S := 25600, lo := ![0, 19540, 0, 18000, 24960, 0, 25280, 0], hi := ![640, 19760, 1280, 18440, 25280, 320, 25600, 640] }
def cert_4068 : Certificate := {
  mu := [(⟨3, by omega⟩, -25600), (⟨6, by omega⟩, -25600), (⟨14, by omega⟩, -25600), (⟨34, by omega⟩, -25600), (⟨89, by omega⟩, -51200)]
  nu := [(⟨0, by omega⟩, -25600), (⟨3, by omega⟩, 25600), (⟨4, by omega⟩, 25600), (⟨10, by omega⟩, -25600), (⟨11, by omega⟩, 25600), (⟨12, by omega⟩, 25600), (⟨15, by omega⟩, -25600), (⟨20, by omega⟩, -25600), (⟨21, by omega⟩, 25600), (⟨22, by omega⟩, 25600), (⟨25, by omega⟩, -25600), (⟨30, by omega⟩, -25600), (⟨33, by omega⟩, 25600), (⟨34, by omega⟩, 25600), (⟨40, by omega⟩, -25600)]
  claimed := 8593735680000
}
def branch_box_4068 : RatBox 8 := { lower := box_4068.profileLo, upper := box_4068.profileHi }
def accepted_4068 : Bool := checkAt 527 1000 box_4068 cert_4068

def box_4070 : Box := { S := 190137139200, lo := ![0, 143494122240, 0, 135324167040, 185383710720, 0, 187760424960, 0], hi := ![4753428480, 145128113280, 9506856960, 136958158080, 187760424960, 2376714240, 190137139200, 4753428480] }
def cert_4070 : Certificate := {
  mu := [(⟨3, by omega⟩, -44270081280), (⟨5, by omega⟩, -9673113600), (⟨6, by omega⟩, -180464025600), (⟨10, by omega⟩, -9673113600), (⟨13, by omega⟩, -188459417600), (⟨22, by omega⟩, -1677721600), (⟨34, by omega⟩, -180464025600), (⟨37, by omega⟩, -9673113600), (⟨42, by omega⟩, -9673113600), (⟨50, by omega⟩, -9673113600), (⟨61, by omega⟩, -9673113600), (⟨74, by omega⟩, -9673113600), (⟨78, by omega⟩, -1677721600), (⟨82, by omega⟩, -9673113600), (⟨89, by omega⟩, -360928051200)]
  nu := [(⟨0, by omega⟩, -180464025600), (⟨3, by omega⟩, 180464025600), (⟨4, by omega⟩, 180464025600), (⟨5, by omega⟩, -9673113600), (⟨10, by omega⟩, -180464025600), (⟨11, by omega⟩, 180464025600), (⟨12, by omega⟩, 180464025600), (⟨13, by omega⟩, 1677721600), (⟨15, by omega⟩, -188459417600), (⟨16, by omega⟩, -1677721600), (⟨18, by omega⟩, -1677721600), (⟨20, by omega⟩, -180464025600), (⟨21, by omega⟩, 180464025600), (⟨22, by omega⟩, 180464025600), (⟨25, by omega⟩, -180464025600), (⟨28, by omega⟩, -9673113600), (⟨30, by omega⟩, -199810252800), (⟨31, by omega⟩, 19346227200), (⟨32, by omega⟩, 19346227200), (⟨33, by omega⟩, 190137139200), (⟨34, by omega⟩, 190137139200), (⟨35, by omega⟩, -9673113600), (⟨36, by omega⟩, -9673113600), (⟨37, by omega⟩, -9673113600), (⟨38, by omega⟩, -9673113600), (⟨39, by omega⟩, -9673113600), (⟨40, by omega⟩, -180464025600)]
  claimed := 3598276785991679150687665520640000
}
def branch_box_4070 : RatBox 8 := { lower := box_4070.profileLo, upper := box_4070.profileHi }
def accepted_4070 : Bool := checkAt 527 1000 box_4070 cert_4070

def box_4072 : Box := { S := 5120, lo := ![0, 3908, 0, 3600, 5056, 0, 4992, 0], hi := ![128, 3952, 256, 3688, 5120, 64, 5120, 128] }
def cert_4072 : Certificate := {
  mu := [(⟨3, by omega⟩, -5120), (⟨4, by omega⟩, -128), (⟨6, by omega⟩, -5120), (⟨34, by omega⟩, -5120), (⟨85, by omega⟩, -5120), (⟨90, by omega⟩, -10240)]
  nu := [(⟨0, by omega⟩, -5120), (⟨3, by omega⟩, 5120), (⟨4, by omega⟩, 5120), (⟨10, by omega⟩, -5120), (⟨12, by omega⟩, 5120), (⟨14, by omega⟩, 5120), (⟨19, by omega⟩, -5120), (⟨20, by omega⟩, -5120), (⟨21, by omega⟩, 5120), (⟨22, by omega⟩, 5120), (⟨25, by omega⟩, -5120), (⟨30, by omega⟩, -5120), (⟨33, by omega⟩, 5120), (⟨34, by omega⟩, 5120), (⟨40, by omega⟩, -5120)]
  claimed := 68707942400
}
def branch_box_4072 : RatBox 8 := { lower := box_4072.profileLo, upper := box_4072.profileHi }
def accepted_4072 : Bool := checkAt 527 1000 box_4072 cert_4072

def box_4074 : Box := { S := 819200, lo := ![0, 618240, 0, 583040, 808960, 0, 798720, 0], hi := ![20480, 625280, 40960, 590080, 819200, 10240, 819200, 20480] }
def cert_4074 : Certificate := {
  mu := [(⟨3, by omega⟩, -200960), (⟨4, by omega⟩, -20480), (⟨6, by omega⟩, -819200), (⟨34, by omega⟩, -819200), (⟨86, by omega⟩, -819200), (⟨90, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -819200), (⟨3, by omega⟩, 819200), (⟨4, by omega⟩, 819200), (⟨10, by omega⟩, -819200), (⟨12, by omega⟩, 819200), (⟨14, by omega⟩, 819200), (⟨19, by omega⟩, -819200), (⟨20, by omega⟩, -819200), (⟨21, by omega⟩, 819200), (⟨22, by omega⟩, 819200), (⟨25, by omega⟩, -819200), (⟨30, by omega⟩, -819200), (⟨33, by omega⟩, 819200), (⟨34, by omega⟩, 819200), (⟨40, by omega⟩, -819200)]
  claimed := 287723214602240000
}
def branch_box_4074 : RatBox 8 := { lower := box_4074.profileLo, upper := box_4074.profileHi }
def accepted_4074 : Bool := checkAt 527 1000 box_4074 cert_4074

def box_4075 : Box := { S := 104678400, lo := ![0, 77200320, 0, 73602000, 99444480, 0, 99444480, 2616960], hi := ![2616960, 80798640, 5233920, 77200320, 102061440, 2616960, 104678400, 5233920] }
def cert_4075 : Certificate := {
  mu := [(⟨3, by omega⟩, -12216240), (⟨5, by omega⟩, -53241600), (⟨6, by omega⟩, -51436800), (⟨10, by omega⟩, -53241600), (⟨21, by omega⟩, -15340800), (⟨22, by omega⟩, -27222400), (⟨34, by omega⟩, -51436800), (⟨38, by omega⟩, -53241600), (⟨42, by omega⟩, -53241600), (⟨50, by omega⟩, -5836800), (⟨53, by omega⟩, -51436800), (⟨69, by omega⟩, -51436800), (⟨74, by omega⟩, -53241600), (⟨77, by omega⟩, -1804800), (⟨82, by omega⟩, -5836800), (⟨85, by omega⟩, -51436800), (⟨89, by omega⟩, -102873600), (⟨93, by omega⟩, -3609600)]
  nu := [(⟨0, by omega⟩, -51436800), (⟨3, by omega⟩, 51436800), (⟨4, by omega⟩, 51436800), (⟨5, by omega⟩, -53241600), (⟨10, by omega⟩, -51436800), (⟨11, by omega⟩, -8873600), (⟨12, by omega⟩, 51436800), (⟨13, by omega⟩, 1804800), (⟨14, by omega⟩, 51436800), (⟨16, by omega⟩, -42563200), (⟨18, by omega⟩, -1804800), (⟨19, by omega⟩, -51436800), (⟨20, by omega⟩, -51436800), (⟨21, by omega⟩, 51436800), (⟨22, by omega⟩, 51436800), (⟨24, by omega⟩, 51436800), (⟨25, by omega⟩, -51436800), (⟨27, by omega⟩, -51436800), (⟨29, by omega⟩, -51436800), (⟨30, by omega⟩, -110515200), (⟨31, by omega⟩, 59078400), (⟨32, by omega⟩, 59078400), (⟨33, by omega⟩, 104678400), (⟨34, by omega⟩, 57273600), (⟨35, by omega⟩, -53241600), (⟨36, by omega⟩, -53241600), (⟨37, by omega⟩, -5836800), (⟨38, by omega⟩, -53241600), (⟨39, by omega⟩, -5836800), (⟨40, by omega⟩, -51436800), (⟨41, by omega⟩, -1804800)]
  claimed := 598890307428579409920000
}
def branch_box_4075 : RatBox 8 := { lower := box_4075.profileLo, upper := box_4075.profileHi }
def accepted_4075 : Bool := checkAt 527 1000 box_4075 cert_4075

def box_4077 : Box := { S := 314035200, lo := ![0, 231600960, 0, 220806000, 306184320, 0, 298333440, 7850880], hi := ![7850880, 242395920, 15701760, 231600960, 314035200, 7850880, 306184320, 15701760] }
def cert_4077 : Certificate := {
  mu := [(⟨3, by omega⟩, -36648720), (⟨5, by omega⟩, -159724800), (⟨6, by omega⟩, -154310400), (⟨10, by omega⟩, -159724800), (⟨21, by omega⟩, -150851200), (⟨34, by omega⟩, -154310400), (⟨38, by omega⟩, -159724800), (⟨42, by omega⟩, -35020800), (⟨46, by omega⟩, -8873600), (⟨50, by omega⟩, -159724800), (⟨53, by omega⟩, -154310400), (⟨61, by omega⟩, -8873600), (⟨69, by omega⟩, -154310400), (⟨74, by omega⟩, -35020800), (⟨77, by omega⟩, -8873600), (⟨82, by omega⟩, -159724800), (⟨85, by omega⟩, -154310400), (⟨89, by omega⟩, -308620800), (⟨93, by omega⟩, -17747200)]
  nu := [(⟨0, by omega⟩, -154310400), (⟨3, by omega⟩, 154310400), (⟨4, by omega⟩, 154310400), (⟨5, by omega⟩, -159724800), (⟨10, by omega⟩, -154310400), (⟨12, by omega⟩, 154310400), (⟨13, by omega⟩, 8873600), (⟨14, by omega⟩, 154310400), (⟨16, by omega⟩, -150851200), (⟨18, by omega⟩, -8873600), (⟨19, by omega⟩, -154310400), (⟨20, by omega⟩, -154310400), (⟨21, by omega⟩, 154310400), (⟨22, by omega⟩, 154310400), (⟨23, by omega⟩, 8873600), (⟨24, by omega⟩, 154310400), (⟨25, by omega⟩, -154310400), (⟨26, by omega⟩, -8873600), (⟨27, by omega⟩, -154310400), (⟨28, by omega⟩, -8873600), (⟨29, by omega⟩, -154310400), (⟨30, by omega⟩, -349056000), (⟨31, by omega⟩, 194745600), (⟨32, by omega⟩, 194745600), (⟨33, by omega⟩, 189331200), (⟨34, by omega⟩, 314035200), (⟨35, by omega⟩, -159724800), (⟨36, by omega⟩, -35020800), (⟨37, by omega⟩, -159724800), (⟨38, by omega⟩, -35020800), (⟨39, by omega⟩, -159724800), (⟨40, by omega⟩, -154310400), (⟨41, by omega⟩, -8873600)]
  claimed := 16170038300571644067840000
}
def branch_box_4077 : RatBox 8 := { lower := box_4077.profileLo, upper := box_4077.profileHi }
def accepted_4077 : Bool := checkAt 527 1000 box_4077 cert_4077

def box_4080 : Box := { S := 150297600, lo := ![0, 113427720, 0, 105678000, 146540160, 0, 146540160, 3757440], hi := ![3757440, 116010960, 7514880, 110844480, 150297600, 3757440, 150297600, 7514880] }
def cert_4080 : Certificate := {
  mu := [(⟨3, by omega⟩, -133079040), (⟨5, by omega⟩, -7782400), (⟨6, by omega⟩, -142515200), (⟨21, by omega⟩, -6963200), (⟨26, by omega⟩, -7782400), (⟨34, by omega⟩, -142515200), (⟨38, by omega⟩, -7782400), (⟨42, by omega⟩, -7782400), (⟨50, by omega⟩, -7782400), (⟨53, by omega⟩, -142515200), (⟨69, by omega⟩, -142515200), (⟨74, by omega⟩, -7782400), (⟨77, by omega⟩, -819200), (⟨82, by omega⟩, -7782400), (⟨85, by omega⟩, -142515200), (⟨89, by omega⟩, -142515200), (⟨90, by omega⟩, -142515200), (⟨93, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -142515200), (⟨3, by omega⟩, 142515200), (⟨4, by omega⟩, 142515200), (⟨7, by omega⟩, -7782400), (⟨10, by omega⟩, -142515200), (⟨12, by omega⟩, 142515200), (⟨13, by omega⟩, 819200), (⟨14, by omega⟩, 142515200), (⟨16, by omega⟩, -6963200), (⟨18, by omega⟩, -819200), (⟨19, by omega⟩, -142515200), (⟨20, by omega⟩, -142515200), (⟨21, by omega⟩, 142515200), (⟨22, by omega⟩, 142515200), (⟨24, by omega⟩, 142515200), (⟨25, by omega⟩, -142515200), (⟨27, by omega⟩, -142515200), (⟨29, by omega⟩, -142515200), (⟨30, by omega⟩, -158080000), (⟨31, by omega⟩, 15564800), (⟨32, by omega⟩, 15564800), (⟨33, by omega⟩, 150297600), (⟨34, by omega⟩, 150297600), (⟨35, by omega⟩, -7782400), (⟨36, by omega⟩, -7782400), (⟨37, by omega⟩, -7782400), (⟨38, by omega⟩, -7782400), (⟨39, by omega⟩, -7782400), (⟨40, by omega⟩, -142515200), (⟨41, by omega⟩, -819200)]
  claimed := 1754968744144319938560000
}
def branch_box_4080 : RatBox 8 := { lower := box_4080.profileLo, upper := box_4080.profileHi }
def accepted_4080 : Bool := checkAt 527 1000 box_4080 cert_4080

def box_4082 : Box := { S := 3164160, lo := ![0, 2333568, 0, 2279184, 3085056, 0, 3085056, 79104], hi := ![79104, 2387952, 158208, 2333568, 3164160, 79104, 3164160, 158208] }
def cert_4082 : Certificate := {
  mu := [(⟨3, by omega⟩, -712576), (⟨5, by omega⟩, -163840), (⟨6, by omega⟩, -3000320), (⟨10, by omega⟩, -163840), (⟨34, by omega⟩, -3000320), (⟨37, by omega⟩, -163840), (⟨42, by omega⟩, -163840), (⟨50, by omega⟩, -163840), (⟨53, by omega⟩, -3000320), (⟨69, by omega⟩, -3000320), (⟨74, by omega⟩, -163840), (⟨82, by omega⟩, -163840), (⟨85, by omega⟩, -3000320), (⟨89, by omega⟩, -3000320), (⟨90, by omega⟩, -3000320)]
  nu := [(⟨0, by omega⟩, -3000320), (⟨3, by omega⟩, 3000320), (⟨4, by omega⟩, 3000320), (⟨5, by omega⟩, -163840), (⟨10, by omega⟩, -3000320), (⟨11, by omega⟩, -704384), (⟨12, by omega⟩, 3000320), (⟨14, by omega⟩, 3000320), (⟨19, by omega⟩, -3000320), (⟨20, by omega⟩, -3000320), (⟨21, by omega⟩, 3000320), (⟨22, by omega⟩, 3000320), (⟨24, by omega⟩, 3000320), (⟨25, by omega⟩, -3000320), (⟨27, by omega⟩, -3000320), (⟨29, by omega⟩, -3000320), (⟨30, by omega⟩, -3328000), (⟨31, by omega⟩, 327680), (⟨32, by omega⟩, 327680), (⟨33, by omega⟩, 3164160), (⟨34, by omega⟩, 3164160), (⟨35, by omega⟩, -163840), (⟨36, by omega⟩, -163840), (⟨37, by omega⟩, -163840), (⟨38, by omega⟩, -163840), (⟨39, by omega⟩, -163840), (⟨40, by omega⟩, -3000320)]
  claimed := 16628348324885299200
}
def branch_box_4082 : RatBox 8 := { lower := box_4082.profileLo, upper := box_4082.profileHi }
def accepted_4082 : Bool := checkAt 527 1000 box_4082 cert_4082

def box_4084 : Box := { S := 1804800, lo := ![0, 1331040, 0, 1269000, 1759680, 22560, 1759680, 45120], hi := ![45120, 1362060, 90240, 1300020, 1804800, 45120, 1804800, 90240] }
def cert_4084 : Certificate := {
  mu := [(⟨3, by omega⟩, -203040), (⟨5, by omega⟩, -902400), (⟨6, by omega⟩, -902400), (⟨10, by omega⟩, -902400), (⟨34, by omega⟩, -902400), (⟨38, by omega⟩, -902400), (⟨42, by omega⟩, -102400), (⟨45, by omega⟩, -902400), (⟨53, by omega⟩, -902400), (⟨61, by omega⟩, -902400), (⟨69, by omega⟩, -902400), (⟨74, by omega⟩, -102400), (⟨77, by omega⟩, -902400), (⟨85, by omega⟩, -902400), (⟨89, by omega⟩, -1804800), (⟨93, by omega⟩, -1804800)]
  nu := [(⟨0, by omega⟩, -902400), (⟨3, by omega⟩, 902400), (⟨4, by omega⟩, 902400), (⟨5, by omega⟩, -902400), (⟨10, by omega⟩, -902400), (⟨12, by omega⟩, 902400), (⟨13, by omega⟩, 902400), (⟨14, by omega⟩, 902400), (⟨18, by omega⟩, -902400), (⟨19, by omega⟩, -902400), (⟨20, by omega⟩, -902400), (⟨21, by omega⟩, 902400), (⟨22, by omega⟩, 902400), (⟨23, by omega⟩, 902400), (⟨24, by omega⟩, 902400), (⟨25, by omega⟩, -902400), (⟨26, by omega⟩, -902400), (⟨27, by omega⟩, -902400), (⟨28, by omega⟩, -902400), (⟨29, by omega⟩, -902400), (⟨30, by omega⟩, -1004800), (⟨31, by omega⟩, 102400), (⟨32, by omega⟩, 102400), (⟨33, by omega⟩, 1004800), (⟨34, by omega⟩, 902400), (⟨35, by omega⟩, -902400), (⟨36, by omega⟩, -102400), (⟨38, by omega⟩, -102400), (⟨40, by omega⟩, -902400), (⟨41, by omega⟩, -902400)]
  claimed := 3085900496732160000
}
def branch_box_4084 : RatBox 8 := { lower := box_4084.profileLo, upper := box_4084.profileHi }
def accepted_4084 : Bool := checkAt 527 1000 box_4084 cert_4084

def box_4086 : Box := { S := 102151680, lo := ![0, 75336864, 0, 71825400, 99597888, 0, 99597888, 3830688], hi := ![2553792, 77092596, 5107584, 73581132, 102151680, 1276896, 102151680, 5107584] }
def cert_4086 : Certificate := {
  mu := [(⟨3, by omega⟩, -11492064), (⟨5, by omega⟩, -51075840), (⟨6, by omega⟩, -51075840), (⟨10, by omega⟩, -51075840), (⟨21, by omega⟩, -48188160), (⟨34, by omega⟩, -51075840), (⟨38, by omega⟩, -51075840), (⟨42, by omega⟩, -5795840), (⟨46, by omega⟩, -2887680), (⟨53, by omega⟩, -51075840), (⟨61, by omega⟩, -2887680), (⟨69, by omega⟩, -51075840), (⟨74, by omega⟩, -5795840), (⟨77, by omega⟩, -2887680), (⟨85, by omega⟩, -51075840), (⟨89, by omega⟩, -102151680), (⟨93, by omega⟩, -5775360)]
  nu := [(⟨0, by omega⟩, -51075840), (⟨3, by omega⟩, 51075840), (⟨4, by omega⟩, 51075840), (⟨5, by omega⟩, -51075840), (⟨10, by omega⟩, -51075840), (⟨12, by omega⟩, 51075840), (⟨13, by omega⟩, 2887680), (⟨14, by omega⟩, 51075840), (⟨16, by omega⟩, -48188160), (⟨18, by omega⟩, -2887680), (⟨19, by omega⟩, -51075840), (⟨20, by omega⟩, -51075840), (⟨21, by omega⟩, 51075840), (⟨22, by omega⟩, 51075840), (⟨23, by omega⟩, 2887680), (⟨24, by omega⟩, 51075840), (⟨25, by omega⟩, -51075840), (⟨26, by omega⟩, -2887680), (⟨27, by omega⟩, -51075840), (⟨28, by omega⟩, -2887680), (⟨29, by omega⟩, -51075840), (⟨30, by omega⟩, -56871680), (⟨31, by omega⟩, 5795840), (⟨32, by omega⟩, 5795840), (⟨33, by omega⟩, 56871680), (⟨34, by omega⟩, 51075840), (⟨35, by omega⟩, -51075840), (⟨36, by omega⟩, -5795840), (⟨38, by omega⟩, -5795840), (⟨40, by omega⟩, -51075840), (⟨41, by omega⟩, -2887680)]
  claimed := 559206985424700447129600
}
def branch_box_4086 : RatBox 8 := { lower := box_4086.profileLo, upper := box_4086.profileHi }
def accepted_4086 : Bool := checkAt 527 1000 box_4086 cert_4086

def box_4087 : Box := { S := 21116160, lo := ![0, 15573168, 0, 14847300, 20588256, 0, 20588256, 527904], hi := ![527904, 15936102, 1055808, 15210234, 20852208, 263952, 21116160, 791856] }
def cert_4087 : Certificate := {
  mu := [(⟨3, by omega⟩, -2486112), (⟨5, by omega⟩, -10648320), (⟨6, by omega⟩, -10467840), (⟨10, by omega⟩, -10648320), (⟨21, by omega⟩, -1596120), (⟨22, by omega⟩, -8961960), (⟨34, by omega⟩, -10467840), (⟨38, by omega⟩, -10648320), (⟨42, by omega⟩, -10648320), (⟨46, by omega⟩, -90240), (⟨50, by omega⟩, -1187840), (⟨53, by omega⟩, -10467840), (⟨61, by omega⟩, -90240), (⟨69, by omega⟩, -10467840), (⟨74, by omega⟩, -10648320), (⟨77, by omega⟩, -90240), (⟨82, by omega⟩, -1187840), (⟨85, by omega⟩, -10467840), (⟨90, by omega⟩, -20935680), (⟨93, by omega⟩, -180480)]
  nu := [(⟨0, by omega⟩, -10467840), (⟨3, by omega⟩, 10467840), (⟨4, by omega⟩, 10467840), (⟨5, by omega⟩, -10648320), (⟨10, by omega⟩, -10467840), (⟨12, by omega⟩, 10467840), (⟨13, by omega⟩, 90240), (⟨14, by omega⟩, 10467840), (⟨16, by omega⟩, -10558080), (⟨18, by omega⟩, -90240), (⟨19, by omega⟩, -10467840), (⟨20, by omega⟩, -10467840), (⟨21, by omega⟩, 10467840), (⟨22, by omega⟩, 10467840), (⟨23, by omega⟩, 90240), (⟨24, by omega⟩, 10467840), (⟨25, by omega⟩, -10467840), (⟨26, by omega⟩, -90240), (⟨27, by omega⟩, -10467840), (⟨28, by omega⟩, -90240), (⟨29, by omega⟩, -10467840), (⟨30, by omega⟩, -22304000), (⟨31, by omega⟩, 11836160), (⟨32, by omega⟩, 11836160), (⟨33, by omega⟩, 21116160), (⟨34, by omega⟩, 11655680), (⟨35, by omega⟩, -10648320), (⟨36, by omega⟩, -10648320), (⟨37, by omega⟩, -1187840), (⟨38, by omega⟩, -10648320), (⟨39, by omega⟩, -1187840), (⟨40, by omega⟩, -10467840), (⟨41, by omega⟩, -90240)]
  claimed := 4943468294666978918400
}
def branch_box_4087 : RatBox 8 := { lower := box_4087.profileLo, upper := box_4087.profileHi }
def accepted_4087 : Bool := checkAt 527 1000 box_4087 cert_4087

def box_4090 : Box := { S := 902400, lo := ![0, 665520, 0, 634500, 891120, 5640, 879840, 22560], hi := ![22560, 681030, 45120, 650010, 902400, 11280, 902400, 33840] }
def cert_4090 : Certificate := {
  mu := [(⟨3, by omega⟩, -104340), (⟨5, by omega⟩, -451200), (⟨6, by omega⟩, -451200), (⟨10, by omega⟩, -451200), (⟨14, by omega⟩, -451200), (⟨21, by omega⟩, -451200), (⟨29, by omega⟩, -451200), (⟨34, by omega⟩, -451200), (⟨38, by omega⟩, -451200), (⟨46, by omega⟩, -451200), (⟨50, by omega⟩, -25600), (⟨53, by omega⟩, -451200), (⟨61, by omega⟩, -451200), (⟨69, by omega⟩, -451200), (⟨77, by omega⟩, -451200), (⟨82, by omega⟩, -25600), (⟨85, by omega⟩, -451200), (⟨90, by omega⟩, -902400), (⟨93, by omega⟩, -902400)]
  nu := [(⟨0, by omega⟩, -451200), (⟨3, by omega⟩, 451200), (⟨4, by omega⟩, 451200), (⟨5, by omega⟩, -451200), (⟨10, by omega⟩, -451200), (⟨11, by omega⟩, 451200), (⟨12, by omega⟩, 451200), (⟨13, by omega⟩, 451200), (⟨14, by omega⟩, 451200), (⟨15, by omega⟩, -451200), (⟨16, by omega⟩, -451200), (⟨17, by omega⟩, -451200), (⟨18, by omega⟩, -451200), (⟨19, by omega⟩, -451200), (⟨20, by omega⟩, -451200), (⟨21, by omega⟩, 451200), (⟨22, by omega⟩, 451200), (⟨23, by omega⟩, 451200), (⟨24, by omega⟩, 451200), (⟨25, by omega⟩, -451200), (⟨26, by omega⟩, -451200), (⟨27, by omega⟩, -451200), (⟨28, by omega⟩, -451200), (⟨29, by omega⟩, -451200), (⟨30, by omega⟩, -476800), (⟨31, by omega⟩, 25600), (⟨32, by omega⟩, 25600), (⟨33, by omega⟩, 451200), (⟨34, by omega⟩, 476800), (⟨35, by omega⟩, -451200), (⟨37, by omega⟩, -25600), (⟨39, by omega⟩, -25600), (⟨40, by omega⟩, -451200), (⟨41, by omega⟩, -451200)]
  claimed := 386828351447040000
}
def branch_box_4090 : RatBox 8 := { lower := box_4090.profileLo, upper := box_4090.profileHi }
def accepted_4090 : Bool := checkAt 527 1000 box_4090 cert_4090

def box_4091 : Box := { S := 67200, lo := ![1680, 49560, 0, 47250, 63840, 0, 63840, 0], hi := ![3360, 51870, 1680, 49560, 67200, 3360, 67200, 3360] }
def cert_4091 : Certificate := {
  mu := [(⟨3, by omega⟩, -55200), (⟨5, by omega⟩, -6400), (⟨6, by omega⟩, -60800), (⟨10, by omega⟩, -6400), (⟨14, by omega⟩, -60800), (⟨30, by omega⟩, -60800), (⟨34, by omega⟩, -60800), (⟨38, by omega⟩, -6400), (⟨42, by omega⟩, -6400), (⟨50, by omega⟩, -6400), (⟨54, by omega⟩, -60800), (⟨69, by omega⟩, -60800), (⟨73, by omega⟩, -6400), (⟨81, by omega⟩, -6400), (⟨85, by omega⟩, -60800), (⟨89, by omega⟩, -60800), (⟨90, by omega⟩, -60800)]
  nu := [(⟨0, by omega⟩, -60800), (⟨3, by omega⟩, 60800), (⟨4, by omega⟩, 60800), (⟨5, by omega⟩, -6400), (⟨10, by omega⟩, -60800), (⟨11, by omega⟩, 60800), (⟨12, by omega⟩, 60800), (⟨14, by omega⟩, 60800), (⟨15, by omega⟩, -60800), (⟨17, by omega⟩, -60800), (⟨19, by omega⟩, -60800), (⟨20, by omega⟩, -60800), (⟨21, by omega⟩, 60800), (⟨22, by omega⟩, 60800), (⟨24, by omega⟩, 60800), (⟨25, by omega⟩, -60800), (⟨27, by omega⟩, -60800), (⟨29, by omega⟩, -60800), (⟨30, by omega⟩, -73600), (⟨31, by omega⟩, 12800), (⟨32, by omega⟩, 12800), (⟨33, by omega⟩, 67200), (⟨34, by omega⟩, 67200), (⟨35, by omega⟩, -6400), (⟨36, by omega⟩, -6400), (⟨37, by omega⟩, -6400), (⟨38, by omega⟩, -6400), (⟨39, by omega⟩, -6400), (⟨40, by omega⟩, -60800)]
  claimed := 156279674880000
}
def branch_box_4091 : RatBox 8 := { lower := box_4091.profileLo, upper := box_4091.profileHi }
def accepted_4091 : Bool := checkAt 527 1000 box_4091 cert_4091

def box_4094 : Box := { S := 50787200, lo := ![1269680, 37455560, 1269680, 35709750, 48247840, 1269680, 48247840, 0], hi := ![2539360, 39201370, 2539360, 37455560, 50787200, 2539360, 50787200, 2539360] }
def cert_4094 : Certificate := {
  mu := [(⟨3, by omega⟩, -7467040), (⟨4, by omega⟩, -10648320), (⟨5, by omega⟩, -24166400), (⟨6, by omega⟩, -26620800), (⟨10, by omega⟩, -24166400), (⟨14, by omega⟩, -26620800), (⟨21, by omega⟩, -26620800), (⟨30, by omega⟩, -26620800), (⟨34, by omega⟩, -26620800), (⟨38, by omega⟩, -24166400), (⟨42, by omega⟩, -24166400), (⟨45, by omega⟩, -26620800), (⟨47, by omega⟩, -10828800), (⟨54, by omega⟩, -26620800), (⟨61, by omega⟩, -26620800), (⟨69, by omega⟩, -26620800), (⟨74, by omega⟩, -24166400), (⟨77, by omega⟩, -26620800), (⟨85, by omega⟩, -26620800), (⟨90, by omega⟩, -53241600), (⟨94, by omega⟩, -53241600)]
  nu := [(⟨0, by omega⟩, -26620800), (⟨3, by omega⟩, 26620800), (⟨4, by omega⟩, 26620800), (⟨5, by omega⟩, -24166400), (⟨10, by omega⟩, -26620800), (⟨11, by omega⟩, 26620800), (⟨12, by omega⟩, 26620800), (⟨13, by omega⟩, 26620800), (⟨14, by omega⟩, 26620800), (⟨15, by omega⟩, -26620800), (⟨16, by omega⟩, -26620800), (⟨17, by omega⟩, -26620800), (⟨18, by omega⟩, -26620800), (⟨19, by omega⟩, -26620800), (⟨20, by omega⟩, -26620800), (⟨21, by omega⟩, 26620800), (⟨22, by omega⟩, 26620800), (⟨23, by omega⟩, 26620800), (⟨24, by omega⟩, 26620800), (⟨25, by omega⟩, -26620800), (⟨26, by omega⟩, -26620800), (⟨27, by omega⟩, -26620800), (⟨28, by omega⟩, -26620800), (⟨29, by omega⟩, -26620800), (⟨30, by omega⟩, -50787200), (⟨31, by omega⟩, 13337600), (⟨32, by omega⟩, 24166400), (⟨33, by omega⟩, 50787200), (⟨34, by omega⟩, 26620800), (⟨35, by omega⟩, -24166400), (⟨36, by omega⟩, -24166400), (⟨37, by omega⟩, 10828800), (⟨38, by omega⟩, -24166400), (⟨40, by omega⟩, -26620800), (⟨41, by omega⟩, -26620800)]
  claimed := 67700627682802800640000
}
def branch_box_4094 : RatBox 8 := { lower := box_4094.profileLo, upper := box_4094.profileHi }
def accepted_4094 : Bool := checkAt 527 1000 box_4094 cert_4094

def box_4096 : Box := { S := 100480, lo := ![2512, 74104, 2512, 70650, 95456, 0, 95456, 2512], hi := ![5024, 77558, 5024, 74104, 100480, 2512, 100480, 5024] }
def cert_4096 : Certificate := {
  mu := [(⟨3, by omega⟩, -78176), (⟨5, by omega⟩, -10240), (⟨6, by omega⟩, -90240), (⟨10, by omega⟩, -10240), (⟨14, by omega⟩, -90240), (⟨29, by omega⟩, -90240), (⟨34, by omega⟩, -90240), (⟨38, by omega⟩, -10240), (⟨42, by omega⟩, -10240), (⟨50, by omega⟩, -10240), (⟨53, by omega⟩, -90240), (⟨69, by omega⟩, -90240), (⟨74, by omega⟩, -10240), (⟨82, by omega⟩, -10240), (⟨85, by omega⟩, -90240), (⟨89, by omega⟩, -90240), (⟨90, by omega⟩, -90240)]
  nu := [(⟨0, by omega⟩, -90240), (⟨3, by omega⟩, 90240), (⟨4, by omega⟩, 90240), (⟨5, by omega⟩, -10240), (⟨10, by omega⟩, -90240), (⟨11, by omega⟩, 90240), (⟨12, by omega⟩, 90240), (⟨14, by omega⟩, 90240), (⟨15, by omega⟩, -90240), (⟨17, by omega⟩, -90240), (⟨19, by omega⟩, -90240), (⟨20, by omega⟩, -90240), (⟨21, by omega⟩, 90240), (⟨22, by omega⟩, 90240), (⟨24, by omega⟩, 90240), (⟨25, by omega⟩, -90240), (⟨27, by omega⟩, -90240), (⟨29, by omega⟩, -90240), (⟨30, by omega⟩, -110720), (⟨31, by omega⟩, 20480), (⟨32, by omega⟩, 20480), (⟨33, by omega⟩, 100480), (⟨34, by omega⟩, 100480), (⟨35, by omega⟩, -10240), (⟨36, by omega⟩, -10240), (⟨37, by omega⟩, -10240), (⟨38, by omega⟩, -10240), (⟨39, by omega⟩, -10240), (⟨40, by omega⟩, -90240)]
  claimed := 526225624678400
}
def branch_box_4096 : RatBox 8 := { lower := box_4096.profileLo, upper := box_4096.profileHi }
def accepted_4096 : Bool := checkAt 527 1000 box_4096 cert_4096

def box_4097 : Box := { S := 4952371200, lo := ![123809280, 3652373760, 123809280, 3482136000, 4704752640, 0, 4704752640, 0], hi := ![247618560, 3822611520, 247618560, 3652373760, 4828561920, 123809280, 4952371200, 123809280] }
def cert_4097 : Certificate := {
  mu := [(⟨3, by omega⟩, -575381520), (⟨5, by omega⟩, -2520403200), (⟨6, by omega⟩, -2431968000), (⟨10, by omega⟩, -2520403200), (⟨14, by omega⟩, -2431968000), (⟨22, by omega⟩, -480076800), (⟨34, by omega⟩, -2431968000), (⟨38, by omega⟩, -2520403200), (⟨42, by omega⟩, -2520403200), (⟨50, by omega⟩, -275968000), (⟨54, by omega⟩, -480076800), (⟨69, by omega⟩, -480076800), (⟨74, by omega⟩, -2520403200), (⟨77, by omega⟩, -45721600), (⟨82, by omega⟩, -275968000), (⟨89, by omega⟩, -4863936000), (⟨93, by omega⟩, -4080652800)]
  nu := [(⟨0, by omega⟩, -2431968000), (⟨3, by omega⟩, 2431968000), (⟨4, by omega⟩, 2431968000), (⟨5, by omega⟩, -2520403200), (⟨10, by omega⟩, -2431968000), (⟨11, by omega⟩, 2431968000), (⟨12, by omega⟩, 2431968000), (⟨13, by omega⟩, 45721600), (⟨15, by omega⟩, -2431968000), (⟨16, by omega⟩, -480076800), (⟨18, by omega⟩, -45721600), (⟨20, by omega⟩, -2431968000), (⟨21, by omega⟩, 2431968000), (⟨22, by omega⟩, 2431968000), (⟨24, by omega⟩, 480076800), (⟨25, by omega⟩, -2431968000), (⟨27, by omega⟩, -480076800), (⟨29, by omega⟩, -480076800), (⟨30, by omega⟩, -5228339200), (⟨31, by omega⟩, 2796371200), (⟨32, by omega⟩, 2796371200), (⟨33, by omega⟩, 4952371200), (⟨34, by omega⟩, 2707936000), (⟨35, by omega⟩, -2520403200), (⟨36, by omega⟩, -2520403200), (⟨37, by omega⟩, -275968000), (⟨38, by omega⟩, -2520403200), (⟨39, by omega⟩, -275968000), (⟨40, by omega⟩, -2431968000), (⟨41, by omega⟩, -2040326400)]
  claimed := 63457838585005173406433280000
}
def branch_box_4097 : RatBox 8 := { lower := box_4097.profileLo, upper := box_4097.profileHi }
def accepted_4097 : Bool := checkAt 527 1000 box_4097 cert_4097

def box_4099 : Box := { S := 755200, lo := ![18880, 556960, 18880, 531000, 736320, 0, 717440, 0], hi := ![37760, 582920, 37760, 556960, 755200, 18880, 736320, 18880] }
def cert_4099 : Certificate := {
  mu := [(⟨3, by omega⟩, -86000), (⟨4, by omega⟩, -165920), (⟨5, by omega⟩, -390400), (⟨6, by omega⟩, -364800), (⟨10, by omega⟩, -390400), (⟨14, by omega⟩, -364800), (⟨22, by omega⟩, -25600), (⟨30, by omega⟩, -364800), (⟨34, by omega⟩, -364800), (⟨38, by omega⟩, -390400), (⟨42, by omega⟩, -390400), (⟨50, by omega⟩, -390400), (⟨54, by omega⟩, -364800), (⟨61, by omega⟩, -25600), (⟨69, by omega⟩, -364800), (⟨73, by omega⟩, -390400), (⟨82, by omega⟩, -390400), (⟨85, by omega⟩, -313600), (⟨86, by omega⟩, -51200), (⟨90, by omega⟩, -780800)]
  nu := [(⟨0, by omega⟩, -390400), (⟨3, by omega⟩, 390400), (⟨4, by omega⟩, 390400), (⟨5, by omega⟩, -390400), (⟨10, by omega⟩, -364800), (⟨11, by omega⟩, 364800), (⟨12, by omega⟩, 364800), (⟨14, by omega⟩, 364800), (⟨15, by omega⟩, -364800), (⟨16, by omega⟩, -25600), (⟨17, by omega⟩, -364800), (⟨19, by omega⟩, -364800), (⟨20, by omega⟩, -364800), (⟨21, by omega⟩, 364800), (⟨22, by omega⟩, 364800), (⟨24, by omega⟩, 364800), (⟨25, by omega⟩, -364800), (⟨27, by omega⟩, -364800), (⟨28, by omega⟩, -25600), (⟨29, by omega⟩, -364800), (⟨30, by omega⟩, -1171200), (⟨31, by omega⟩, 780800), (⟨32, by omega⟩, 780800), (⟨33, by omega⟩, 780800), (⟨34, by omega⟩, 780800), (⟨35, by omega⟩, -390400), (⟨36, by omega⟩, -390400), (⟨37, by omega⟩, -390400), (⟨38, by omega⟩, -390400), (⟨39, by omega⟩, -390400), (⟨40, by omega⟩, -390400)]
  claimed := 222756624302080000
}
def branch_box_4099 : RatBox 8 := { lower := box_4099.profileLo, upper := box_4099.profileHi }
def accepted_4099 : Bool := checkAt 527 1000 box_4099 cert_4099

end PeaceableQueens.UpperBound.Generated.Even.Core
