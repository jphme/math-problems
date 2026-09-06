import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_3302 : Box := { S := 76711219200, lo := ![958890240, 53937576000, 3835560960, 56574524160, 74793438720, 958890240, 74793438720, 0], hi := ![1917780480, 55256050080, 4794451200, 57892998240, 76711219200, 1917780480, 76711219200, 1917780480] }
def cert_3302 : Certificate := {
  mu := [(⟨4, by omega⟩, -16179456720), (⟨5, by omega⟩, -42423628800), (⟨6, by omega⟩, -34287590400), (⟨9, by omega⟩, -42423628800), (⟨13, by omega⟩, -34287590400), (⟨21, by omega⟩, -34287590400), (⟨30, by omega⟩, -34287590400), (⟨33, by omega⟩, -34287590400), (⟨37, by omega⟩, -42423628800), (⟨42, by omega⟩, -40610124800), (⟨45, by omega⟩, -34287590400), (⟨54, by omega⟩, -34287590400), (⟨61, by omega⟩, -34287590400), (⟨70, by omega⟩, -34287590400), (⟨74, by omega⟩, -40610124800), (⟨78, by omega⟩, -34287590400), (⟨80, by omega⟩, -21438617600), (⟨86, by omega⟩, -34287590400), (⟨89, by omega⟩, -68575180800), (⟨94, by omega⟩, -68575180800)]
  nu := [(⟨0, by omega⟩, -34287590400), (⟨3, by omega⟩, 34287590400), (⟨4, by omega⟩, 34287590400), (⟨5, by omega⟩, -42423628800), (⟨10, by omega⟩, -34287590400), (⟨11, by omega⟩, 34287590400), (⟨12, by omega⟩, 34287590400), (⟨13, by omega⟩, 34287590400), (⟨14, by omega⟩, 34287590400), (⟨15, by omega⟩, -34287590400), (⟨16, by omega⟩, -34287590400), (⟨17, by omega⟩, -34287590400), (⟨18, by omega⟩, -34287590400), (⟨19, by omega⟩, -34287590400), (⟨20, by omega⟩, -34287590400), (⟨21, by omega⟩, 34287590400), (⟨22, by omega⟩, 34287590400), (⟨23, by omega⟩, 34287590400), (⟨24, by omega⟩, 34287590400), (⟨25, by omega⟩, -34287590400), (⟨26, by omega⟩, -34287590400), (⟨27, by omega⟩, -34287590400), (⟨28, by omega⟩, -34287590400), (⟨29, by omega⟩, -34287590400), (⟨30, by omega⟩, -74897715200), (⟨31, by omega⟩, 40610124800), (⟨32, by omega⟩, 19171507200), (⟨33, by omega⟩, 74897715200), (⟨34, by omega⟩, 34287590400), (⟨35, by omega⟩, -42423628800), (⟨36, by omega⟩, -40610124800), (⟨38, by omega⟩, -40610124800), (⟨39, by omega⟩, 21438617600), (⟨40, by omega⟩, -34287590400), (⟨41, by omega⟩, -34287590400)]
  claimed := 236375669702957361580977684480000
}
def branch_box_3302 : RatBox 8 := { lower := box_3302.profileLo, upper := box_3302.profileHi }
def accepted_3302 : Bool := checkAt 527 1000 box_3302 cert_3302

def box_3303 : Box := { S := 60460800, lo := ![755760, 42511500, 3023040, 44589840, 58949280, 0, 58949280, 0], hi := ![1511520, 43550670, 3778800, 45629010, 59705040, 755760, 60460800, 1511520] }
def cert_3303 : Certificate := {
  mu := [(⟨5, by omega⟩, -34291200), (⟨6, by omega⟩, -26169600), (⟨9, by omega⟩, -34291200), (⟨13, by omega⟩, -26169600), (⟨22, by omega⟩, -26169600), (⟨30, by omega⟩, -4060800), (⟨33, by omega⟩, -26169600), (⟨37, by omega⟩, -34291200), (⟨42, by omega⟩, -34291200), (⟨50, by omega⟩, -2969600), (⟨53, by omega⟩, -26169600), (⟨61, by omega⟩, -4060800), (⟨70, by omega⟩, -26169600), (⟨74, by omega⟩, -34291200), (⟨78, by omega⟩, -26169600), (⟨82, by omega⟩, -2969600), (⟨86, by omega⟩, -4060800), (⟨90, by omega⟩, -52339200), (⟨93, by omega⟩, -8121600)]
  nu := [(⟨0, by omega⟩, -26169600), (⟨3, by omega⟩, 26169600), (⟨4, by omega⟩, 26169600), (⟨5, by omega⟩, -34291200), (⟨10, by omega⟩, -26169600), (⟨11, by omega⟩, 26169600), (⟨12, by omega⟩, 26169600), (⟨13, by omega⟩, 26169600), (⟨14, by omega⟩, 4060800), (⟨15, by omega⟩, -26169600), (⟨16, by omega⟩, -26169600), (⟨17, by omega⟩, -4060800), (⟨18, by omega⟩, -26169600), (⟨19, by omega⟩, -4060800), (⟨20, by omega⟩, -26169600), (⟨21, by omega⟩, 26169600), (⟨22, by omega⟩, 26169600), (⟨24, by omega⟩, 26169600), (⟨25, by omega⟩, -26169600), (⟨27, by omega⟩, -26169600), (⟨28, by omega⟩, -4060800), (⟨29, by omega⟩, -26169600), (⟨30, by omega⟩, -63430400), (⟨31, by omega⟩, 37260800), (⟨32, by omega⟩, 37260800), (⟨33, by omega⟩, 60460800), (⟨34, by omega⟩, 29139200), (⟨35, by omega⟩, -34291200), (⟨36, by omega⟩, -34291200), (⟨37, by omega⟩, -2969600), (⟨38, by omega⟩, -34291200), (⟨39, by omega⟩, -2969600), (⟨40, by omega⟩, -26169600), (⟨41, by omega⟩, -4060800)]
  claimed := 116167379543256637440000
}
def branch_box_3303 : RatBox 8 := { lower := box_3303.profileLo, upper := box_3303.profileHi }
def accepted_3303 : Bool := checkAt 527 1000 box_3303 cert_3303

def box_3306 : Box := { S := 10875724800, lo := ![135946560, 7646994000, 679732800, 8020847040, 10603831680, 135946560, 10603831680, 0], hi := ![271893120, 7833920520, 815679360, 8207773560, 10875724800, 271893120, 10875724800, 271893120] }
def cert_3306 : Certificate := {
  mu := [(⟨4, by omega⟩, -2250123120), (⟨5, by omega⟩, -5977497600), (⟨6, by omega⟩, -4898227200), (⟨9, by omega⟩, -5977497600), (⟨13, by omega⟩, -4898227200), (⟨21, by omega⟩, -4898227200), (⟨30, by omega⟩, -4898227200), (⟨33, by omega⟩, -4898227200), (⟨37, by omega⟩, -5977497600), (⟨42, by omega⟩, -5662489600), (⟨45, by omega⟩, -4898227200), (⟨54, by omega⟩, -4898227200), (⟨61, by omega⟩, -4898227200), (⟨70, by omega⟩, -4898227200), (⟨74, by omega⟩, -5662489600), (⟨78, by omega⟩, -4898227200), (⟨80, by omega⟩, -2981529600), (⟨86, by omega⟩, -4898227200), (⟨89, by omega⟩, -9796454400), (⟨94, by omega⟩, -9796454400)]
  nu := [(⟨0, by omega⟩, -4898227200), (⟨3, by omega⟩, 4898227200), (⟨4, by omega⟩, 4898227200), (⟨5, by omega⟩, -5977497600), (⟨10, by omega⟩, -4898227200), (⟨11, by omega⟩, 4898227200), (⟨12, by omega⟩, 4898227200), (⟨13, by omega⟩, 4898227200), (⟨14, by omega⟩, 4898227200), (⟨15, by omega⟩, -4898227200), (⟨16, by omega⟩, -4898227200), (⟨17, by omega⟩, -4898227200), (⟨18, by omega⟩, -4898227200), (⟨19, by omega⟩, -4898227200), (⟨20, by omega⟩, -4898227200), (⟨21, by omega⟩, 4898227200), (⟨22, by omega⟩, 4898227200), (⟨23, by omega⟩, 4898227200), (⟨24, by omega⟩, 4898227200), (⟨25, by omega⟩, -4898227200), (⟨26, by omega⟩, -4898227200), (⟨27, by omega⟩, -4898227200), (⟨28, by omega⟩, -4898227200), (⟨29, by omega⟩, -4898227200), (⟨30, by omega⟩, -10560716800), (⟨31, by omega⟩, 5662489600), (⟨32, by omega⟩, 2680960000), (⟨33, by omega⟩, 10560716800), (⟨34, by omega⟩, 4898227200), (⟨35, by omega⟩, -5977497600), (⟨36, by omega⟩, -5662489600), (⟨38, by omega⟩, -5662489600), (⟨39, by omega⟩, 2981529600), (⟨40, by omega⟩, -4898227200), (⟨41, by omega⟩, -4898227200)]
  claimed := 671783176003041990847365120000
}
def branch_box_3306 : RatBox 8 := { lower := box_3306.profileLo, upper := box_3306.profileHi }
def accepted_3306 : Bool := checkAt 527 1000 box_3306 cert_3306

def box_3307 : Box := { S := 60009600, lo := ![750120, 42194250, 3750600, 44257080, 58509360, 0, 58509360, 0], hi := ![1500240, 43225665, 4500720, 45288495, 59259480, 750120, 60009600, 1500240] }
def cert_3307 : Certificate := {
  mu := [(⟨5, by omega⟩, -33840000), (⟨6, by omega⟩, -26169600), (⟨9, by omega⟩, -33840000), (⟨13, by omega⟩, -26169600), (⟨22, by omega⟩, -26169600), (⟨30, by omega⟩, -3835200), (⟨33, by omega⟩, -26169600), (⟨37, by omega⟩, -33840000), (⟨42, by omega⟩, -33840000), (⟨50, by omega⟩, -2969600), (⟨53, by omega⟩, -26169600), (⟨61, by omega⟩, -3835200), (⟨70, by omega⟩, -26169600), (⟨74, by omega⟩, -33840000), (⟨78, by omega⟩, -26169600), (⟨82, by omega⟩, -2969600), (⟨86, by omega⟩, -3835200), (⟨90, by omega⟩, -52339200), (⟨93, by omega⟩, -7670400)]
  nu := [(⟨0, by omega⟩, -26169600), (⟨3, by omega⟩, 26169600), (⟨4, by omega⟩, 26169600), (⟨5, by omega⟩, -33840000), (⟨10, by omega⟩, -26169600), (⟨11, by omega⟩, 26169600), (⟨12, by omega⟩, 26169600), (⟨13, by omega⟩, 26169600), (⟨14, by omega⟩, 3835200), (⟨15, by omega⟩, -26169600), (⟨16, by omega⟩, -26169600), (⟨17, by omega⟩, -3835200), (⟨18, by omega⟩, -26169600), (⟨19, by omega⟩, -3835200), (⟨20, by omega⟩, -26169600), (⟨21, by omega⟩, 26169600), (⟨22, by omega⟩, 26169600), (⟨24, by omega⟩, 26169600), (⟨25, by omega⟩, -26169600), (⟨27, by omega⟩, -26169600), (⟨28, by omega⟩, -3835200), (⟨29, by omega⟩, -26169600), (⟨30, by omega⟩, -62979200), (⟨31, by omega⟩, 36809600), (⟨32, by omega⟩, 36809600), (⟨33, by omega⟩, 60009600), (⟨34, by omega⟩, 29139200), (⟨35, by omega⟩, -33840000), (⟨36, by omega⟩, -33840000), (⟨37, by omega⟩, -2969600), (⟨38, by omega⟩, -33840000), (⟨39, by omega⟩, -2969600), (⟨40, by omega⟩, -26169600), (⟨41, by omega⟩, -3835200)]
  claimed := 113274692804056412160000
}
def branch_box_3307 : RatBox 8 := { lower := box_3307.profileLo, upper := box_3307.profileHi }
def accepted_3307 : Bool := checkAt 527 1000 box_3307 cert_3307

def box_3310 : Box := { S := 9764419200, lo := ![183082860, 6865607250, 610276200, 7201259160, 9642363960, 0, 9520308720, 0], hi := ![244110480, 7033433205, 732331440, 7369085115, 9764419200, 122055240, 9764419200, 244110480] }
def cert_3310 : Certificate := {
  mu := [(⟨5, by omega⟩, -5465160000), (⟨6, by omega⟩, -4299259200), (⟨9, by omega⟩, -5465160000), (⟨13, by omega⟩, -4299259200), (⟨21, by omega⟩, -1108147200), (⟨30, by omega⟩, -4299259200), (⟨33, by omega⟩, -4299259200), (⟨37, by omega⟩, -5465160000), (⟨42, by omega⟩, -487859200), (⟨45, by omega⟩, -57753600), (⟨53, by omega⟩, -4299259200), (⟨62, by omega⟩, -57753600), (⟨70, by omega⟩, -5349652800), (⟨74, by omega⟩, -487859200), (⟨78, by omega⟩, -57753600), (⟨86, by omega⟩, -4299259200), (⟨89, by omega⟩, -8598518400), (⟨93, by omega⟩, -115507200)]
  nu := [(⟨0, by omega⟩, -4299259200), (⟨3, by omega⟩, 4299259200), (⟨4, by omega⟩, 4299259200), (⟨5, by omega⟩, -5465160000), (⟨10, by omega⟩, -4299259200), (⟨11, by omega⟩, 4299259200), (⟨12, by omega⟩, 4299259200), (⟨13, by omega⟩, 57753600), (⟨14, by omega⟩, 4299259200), (⟨15, by omega⟩, -4299259200), (⟨16, by omega⟩, -1108147200), (⟨17, by omega⟩, -4299259200), (⟨18, by omega⟩, -57753600), (⟨19, by omega⟩, -4299259200), (⟨20, by omega⟩, -4299259200), (⟨21, by omega⟩, 4299259200), (⟨22, by omega⟩, 4299259200), (⟨23, by omega⟩, 57753600), (⟨24, by omega⟩, 4299259200), (⟨25, by omega⟩, -4299259200), (⟨26, by omega⟩, -57753600), (⟨27, by omega⟩, -4299259200), (⟨28, by omega⟩, -57753600), (⟨29, by omega⟩, -5349652800), (⟨30, by omega⟩, -4787118400), (⟨31, by omega⟩, 487859200), (⟨32, by omega⟩, 487859200), (⟨33, by omega⟩, 4787118400), (⟨34, by omega⟩, 4299259200), (⟨35, by omega⟩, -5465160000), (⟨36, by omega⟩, -487859200), (⟨38, by omega⟩, -487859200), (⟨40, by omega⟩, -4299259200), (⟨41, by omega⟩, -57753600)]
  claimed := 490482787995123045666693120000
}
def branch_box_3310 : RatBox 8 := { lower := box_3310.profileLo, upper := box_3310.profileHi }
def accepted_3310 : Bool := checkAt 527 1000 box_3310 cert_3310

def box_3312 : Box := { S := 481881600, lo := ![6023520, 338823000, 33129360, 355387680, 475858080, 0, 469834560, 0], hi := ![9035280, 347105340, 36141120, 363670020, 481881600, 6023520, 481881600, 12047040] }
def cert_3312 : Certificate := {
  mu := [(⟨5, by omega⟩, -268915200), (⟨6, by omega⟩, -212966400), (⟨9, by omega⟩, -268915200), (⟨13, by omega⟩, -212966400), (⟨21, by omega⟩, -212966400), (⟨30, by omega⟩, -212966400), (⟨33, by omega⟩, -212966400), (⟨37, by omega⟩, -268915200), (⟨42, by omega⟩, -24166400), (⟨70, by omega⟩, -55948800), (⟨74, by omega⟩, -24166400), (⟨78, by omega⟩, -212966400), (⟨86, by omega⟩, -212966400), (⟨89, by omega⟩, -425932800), (⟨93, by omega⟩, -425932800)]
  nu := [(⟨0, by omega⟩, -212966400), (⟨3, by omega⟩, 212966400), (⟨4, by omega⟩, 212966400), (⟨5, by omega⟩, -268915200), (⟨10, by omega⟩, -212966400), (⟨11, by omega⟩, 212966400), (⟨12, by omega⟩, 212966400), (⟨13, by omega⟩, 212966400), (⟨14, by omega⟩, 212966400), (⟨15, by omega⟩, -212966400), (⟨16, by omega⟩, -212966400), (⟨17, by omega⟩, -212966400), (⟨18, by omega⟩, -212966400), (⟨19, by omega⟩, -212966400), (⟨20, by omega⟩, -212966400), (⟨21, by omega⟩, 212966400), (⟨22, by omega⟩, 212966400), (⟨25, by omega⟩, -212966400), (⟨29, by omega⟩, -55948800), (⟨30, by omega⟩, -237132800), (⟨31, by omega⟩, 24166400), (⟨32, by omega⟩, 24166400), (⟨33, by omega⟩, 237132800), (⟨34, by omega⟩, 212966400), (⟨35, by omega⟩, -268915200), (⟨36, by omega⟩, -24166400), (⟨38, by omega⟩, -24166400), (⟨40, by omega⟩, -212966400), (⟨41, by omega⟩, -212966400)]
  claimed := 58925797213887248302080000
}
def branch_box_3312 : RatBox 8 := { lower := box_3312.profileLo, upper := box_3312.profileHi }
def accepted_3312 : Bool := checkAt 527 1000 box_3312 cert_3312

def box_3314 : Box := { S := 15820800, lo := ![197760, 11124000, 791040, 11939760, 15425280, 0, 15425280, 0], hi := ![395520, 11395920, 1186560, 12211680, 15820800, 395520, 15820800, 395520] }
def cert_3314 : Certificate := {
  mu := [(⟨5, by omega⟩, -819200), (⟨6, by omega⟩, -15001600), (⟨10, by omega⟩, -819200), (⟨14, by omega⟩, -15001600), (⟨22, by omega⟩, -15001600), (⟨34, by omega⟩, -15001600), (⟨37, by omega⟩, -819200), (⟨42, by omega⟩, -819200), (⟨50, by omega⟩, -819200), (⟨62, by omega⟩, -819200), (⟨74, by omega⟩, -819200), (⟨78, by omega⟩, -15001600), (⟨82, by omega⟩, -819200), (⟨89, by omega⟩, -15001600), (⟨90, by omega⟩, -15001600)]
  nu := [(⟨0, by omega⟩, -15001600), (⟨3, by omega⟩, 15001600), (⟨4, by omega⟩, 15001600), (⟨5, by omega⟩, -819200), (⟨10, by omega⟩, -15001600), (⟨11, by omega⟩, 15001600), (⟨12, by omega⟩, 15001600), (⟨13, by omega⟩, 15001600), (⟨15, by omega⟩, -15001600), (⟨16, by omega⟩, -15001600), (⟨18, by omega⟩, -15001600), (⟨20, by omega⟩, -15001600), (⟨21, by omega⟩, 15001600), (⟨22, by omega⟩, 15001600), (⟨25, by omega⟩, -15001600), (⟨28, by omega⟩, -819200), (⟨30, by omega⟩, -16640000), (⟨31, by omega⟩, 1638400), (⟨32, by omega⟩, 1638400), (⟨33, by omega⟩, 15820800), (⟨34, by omega⟩, 15820800), (⟨35, by omega⟩, -819200), (⟨36, by omega⟩, -819200), (⟨37, by omega⟩, -819200), (⟨38, by omega⟩, -819200), (⟨39, by omega⟩, -819200), (⟨40, by omega⟩, -15001600)]
  claimed := 2077523827729367040000
}
def branch_box_3314 : RatBox 8 := { lower := box_3314.profileLo, upper := box_3314.profileHi }
def accepted_3314 : Bool := checkAt 527 1000 box_3314 cert_3314

def box_3316 : Box := { S := 2357299200, lo := ![0, 1657476000, 117864960, 1779024240, 2298366720, 29466240, 2298366720, 0], hi := ![29466240, 1697992080, 176797440, 1819540320, 2357299200, 58932480, 2357299200, 58932480] }
def cert_3316 : Certificate := {
  mu := [(⟨4, by omega⟩, -55880960), (⟨5, by omega⟩, -122060800), (⟨6, by omega⟩, -2235238400), (⟨9, by omega⟩, -122060800), (⟨13, by omega⟩, -26214400), (⟨21, by omega⟩, -26214400), (⟨29, by omega⟩, -26214400), (⟨33, by omega⟩, -2235238400), (⟨37, by omega⟩, -122060800), (⟨42, by omega⟩, -122060800), (⟨46, by omega⟩, -2235238400), (⟨50, by omega⟩, -122060800), (⟨61, by omega⟩, -2235238400), (⟨74, by omega⟩, -122060800), (⟨77, by omega⟩, -2235238400), (⟨82, by omega⟩, -122060800), (⟨85, by omega⟩, -2235238400), (⟨90, by omega⟩, -4470476800), (⟨94, by omega⟩, -4470476800)]
  nu := [(⟨0, by omega⟩, -2235238400), (⟨3, by omega⟩, 2235238400), (⟨4, by omega⟩, 2235238400), (⟨5, by omega⟩, -122060800), (⟨10, by omega⟩, -2235238400), (⟨11, by omega⟩, 26214400), (⟨12, by omega⟩, 2235238400), (⟨13, by omega⟩, 2235238400), (⟨14, by omega⟩, 2235238400), (⟨15, by omega⟩, -26214400), (⟨16, by omega⟩, -26214400), (⟨17, by omega⟩, -26214400), (⟨18, by omega⟩, -2235238400), (⟨19, by omega⟩, -2235238400), (⟨20, by omega⟩, -2235238400), (⟨21, by omega⟩, 2235238400), (⟨22, by omega⟩, 2235238400), (⟨23, by omega⟩, 2235238400), (⟨25, by omega⟩, -2235238400), (⟨26, by omega⟩, -2235238400), (⟨28, by omega⟩, -2235238400), (⟨30, by omega⟩, -2479360000), (⟨31, by omega⟩, 244121600), (⟨32, by omega⟩, 244121600), (⟨33, by omega⟩, 2357299200), (⟨34, by omega⟩, 2357299200), (⟨35, by omega⟩, -122060800), (⟨36, by omega⟩, -122060800), (⟨37, by omega⟩, -122060800), (⟨38, by omega⟩, -122060800), (⟨39, by omega⟩, -122060800), (⟨40, by omega⟩, -2235238400), (⟨41, by omega⟩, -2235238400)]
  claimed := 6829707274732107918213120000
}
def branch_box_3316 : RatBox 8 := { lower := box_3316.profileLo, upper := box_3316.profileHi }
def accepted_3316 : Bool := checkAt 527 1000 box_3316 cert_3316

def box_3317 : Box := { S := 8390582400, lo := ![0, 5899628250, 419529120, 6332267655, 8180817840, 0, 8180817840, 0], hi := ![104882280, 6043841385, 629293680, 6476480790, 8285700120, 104882280, 8390582400, 209764560] }
def cert_3317 : Certificate := {
  mu := [(⟨5, by omega⟩, -4710502400), (⟨6, by omega⟩, -3680080000), (⟨9, by omega⟩, -4710502400), (⟨13, by omega⟩, -960102400), (⟨21, by omega⟩, -4710502400), (⟨33, by omega⟩, -3680080000), (⟨37, by omega⟩, -4710502400), (⟨42, by omega⟩, -4710502400), (⟨50, by omega⟩, -401920000), (⟨61, by omega⟩, -4710502400), (⟨74, by omega⟩, -4710502400), (⟨78, by omega⟩, -3680080000), (⟨82, by omega⟩, -401920000), (⟨90, by omega⟩, -7360160000)]
  nu := [(⟨0, by omega⟩, -3680080000), (⟨3, by omega⟩, 3680080000), (⟨4, by omega⟩, 3680080000), (⟨5, by omega⟩, -4710502400), (⟨10, by omega⟩, -3680080000), (⟨11, by omega⟩, 960102400), (⟨12, by omega⟩, 3680080000), (⟨13, by omega⟩, 3680080000), (⟨15, by omega⟩, -960102400), (⟨16, by omega⟩, -4710502400), (⟨18, by omega⟩, -3680080000), (⟨20, by omega⟩, -3680080000), (⟨21, by omega⟩, 3680080000), (⟨22, by omega⟩, 3680080000), (⟨25, by omega⟩, -3680080000), (⟨28, by omega⟩, -4710502400), (⟨30, by omega⟩, -8792502400), (⟨31, by omega⟩, 5112422400), (⟨32, by omega⟩, 5112422400), (⟨33, by omega⟩, 8390582400), (⟨34, by omega⟩, 4082000000), (⟨35, by omega⟩, -4710502400), (⟨36, by omega⟩, -4710502400), (⟨37, by omega⟩, -401920000), (⟨38, by omega⟩, -4710502400), (⟨39, by omega⟩, -401920000), (⟨40, by omega⟩, -3680080000)]
  claimed := 310703877847039402227824640000
}
def branch_box_3317 : RatBox 8 := { lower := box_3317.profileLo, upper := box_3317.profileHi }
def accepted_3317 : Bool := checkAt 527 1000 box_3317 cert_3317

def box_3320 : Box := { S := 25600, lo := ![0, 18220, 1280, 19320, 25280, 0, 24960, 0], hi := ![320, 18440, 1920, 19760, 25600, 320, 25600, 640] }
def cert_3320 : Certificate := {
  mu := [(⟨4, by omega⟩, -640), (⟨6, by omega⟩, -25600), (⟨13, by omega⟩, -25600), (⟨29, by omega⟩, -25600), (⟨33, by omega⟩, -25600), (⟨85, by omega⟩, -25600), (⟨90, by omega⟩, -51200), (⟨93, by omega⟩, -390400)]
  nu := [(⟨0, by omega⟩, -25600), (⟨3, by omega⟩, 25600), (⟨4, by omega⟩, 25600), (⟨10, by omega⟩, -25600), (⟨11, by omega⟩, 25600), (⟨12, by omega⟩, 25600), (⟨14, by omega⟩, 25600), (⟨15, by omega⟩, -25600), (⟨17, by omega⟩, -25600), (⟨19, by omega⟩, -25600), (⟨20, by omega⟩, -25600), (⟨21, by omega⟩, 25600), (⟨22, by omega⟩, 25600), (⟨25, by omega⟩, -25600), (⟨30, by omega⟩, -25600), (⟨33, by omega⟩, 25600), (⟨34, by omega⟩, 25600), (⟨40, by omega⟩, -25600)]
  claimed := 8715632640000
}
def branch_box_3320 : RatBox 8 := { lower := box_3320.profileLo, upper := box_3320.profileHi }
def accepted_3320 : Bool := checkAt 527 1000 box_3320 cert_3320

def box_3322 : Box := { S := 6400, lo := ![0, 4500, 320, 4885, 6320, 0, 6240, 0], hi := ![80, 4555, 480, 4940, 6400, 80, 6400, 160] }
def cert_3322 : Certificate := {
  mu := [(⟨4, by omega⟩, -160), (⟨6, by omega⟩, -6400), (⟨33, by omega⟩, -6400), (⟨53, by omega⟩, -6400), (⟨70, by omega⟩, -6400), (⟨78, by omega⟩, -6400), (⟨85, by omega⟩, -6400), (⟨90, by omega⟩, -12800), (⟨93, by omega⟩, -226000)]
  nu := [(⟨0, by omega⟩, -6400), (⟨3, by omega⟩, 6400), (⟨4, by omega⟩, 6400), (⟨10, by omega⟩, -6400), (⟨12, by omega⟩, 6400), (⟨13, by omega⟩, 6400), (⟨14, by omega⟩, 6400), (⟨18, by omega⟩, -6400), (⟨19, by omega⟩, -6400), (⟨20, by omega⟩, -6400), (⟨21, by omega⟩, 6400), (⟨22, by omega⟩, 6400), (⟨24, by omega⟩, 6400), (⟨25, by omega⟩, -6400), (⟨27, by omega⟩, -6400), (⟨29, by omega⟩, -6400), (⟨30, by omega⟩, -6400), (⟨33, by omega⟩, 6400), (⟨34, by omega⟩, 6400), (⟨40, by omega⟩, -6400), (⟨41, by omega⟩, -6400)]
  claimed := 136069120000
}
def branch_box_3322 : RatBox 8 := { lower := box_3322.profileLo, upper := box_3322.profileHi }
def accepted_3322 : Bool := checkAt 527 1000 box_3322 cert_3322

def box_3324 : Box := { S := 12800, lo := ![0, 9220, 640, 9660, 12480, 0, 12480, 0], hi := ![320, 9440, 960, 9880, 12800, 320, 12800, 320] }
def cert_3324 : Certificate := {
  mu := [(⟨6, by omega⟩, -12800), (⟨33, by omega⟩, -12800), (⟨89, by omega⟩, -25600)]
  nu := [(⟨0, by omega⟩, -12800), (⟨3, by omega⟩, 12800), (⟨4, by omega⟩, 12800), (⟨10, by omega⟩, -12800), (⟨12, by omega⟩, 12800), (⟨20, by omega⟩, -12800), (⟨21, by omega⟩, 12800), (⟨22, by omega⟩, 12800), (⟨25, by omega⟩, -12800), (⟨30, by omega⟩, -12800), (⟨33, by omega⟩, 12800), (⟨34, by omega⟩, 12800), (⟨40, by omega⟩, -12800)]
  claimed := 1074298880000
}
def branch_box_3324 : RatBox 8 := { lower := box_3324.profileLo, upper := box_3324.profileHi }
def accepted_3324 : Bool := checkAt 527 1000 box_3324 cert_3324

def box_3326 : Box := { S := 3955200, lo := ![49440, 2848980, 197760, 2916960, 3856320, 0, 3856320, 0], hi := ![98880, 2916960, 296640, 2984940, 3955200, 98880, 3955200, 98880] }
def cert_3326 : Certificate := {
  mu := [(⟨5, by omega⟩, -204800), (⟨6, by omega⟩, -3750400), (⟨10, by omega⟩, -204800), (⟨14, by omega⟩, -3750400), (⟨22, by omega⟩, -3750400), (⟨34, by omega⟩, -3750400), (⟨37, by omega⟩, -204800), (⟨42, by omega⟩, -204800), (⟨50, by omega⟩, -204800), (⟨62, by omega⟩, -204800), (⟨74, by omega⟩, -204800), (⟨78, by omega⟩, -3750400), (⟨82, by omega⟩, -204800), (⟨89, by omega⟩, -3750400), (⟨90, by omega⟩, -3750400)]
  nu := [(⟨0, by omega⟩, -3750400), (⟨3, by omega⟩, 3750400), (⟨4, by omega⟩, 3750400), (⟨5, by omega⟩, -204800), (⟨10, by omega⟩, -3750400), (⟨11, by omega⟩, 3750400), (⟨12, by omega⟩, 3750400), (⟨13, by omega⟩, 3750400), (⟨15, by omega⟩, -3750400), (⟨16, by omega⟩, -3750400), (⟨18, by omega⟩, -3750400), (⟨20, by omega⟩, -3750400), (⟨21, by omega⟩, 3750400), (⟨22, by omega⟩, 3750400), (⟨25, by omega⟩, -3750400), (⟨28, by omega⟩, -204800), (⟨30, by omega⟩, -4160000), (⟨31, by omega⟩, 409600), (⟨32, by omega⟩, 409600), (⟨33, by omega⟩, 3955200), (⟨34, by omega⟩, 3955200), (⟨35, by omega⟩, -204800), (⟨36, by omega⟩, -204800), (⟨37, by omega⟩, -204800), (⟨38, by omega⟩, -204800), (⟨39, by omega⟩, -204800), (⟨40, by omega⟩, -3750400)]
  claimed := 32501017193840640000
}
def branch_box_3326 : RatBox 8 := { lower := box_3326.profileLo, upper := box_3326.profileHi }
def accepted_3326 : Bool := checkAt 527 1000 box_3326 cert_3326

def box_3328 : Box := { S := 15820800, lo := ![0, 11395920, 791040, 11667840, 15425280, 197760, 15425280, 0], hi := ![197760, 11667840, 1186560, 11939760, 15820800, 395520, 15820800, 395520] }
def cert_3328 : Certificate := {
  mu := [(⟨4, by omega⟩, -375040), (⟨5, by omega⟩, -819200), (⟨6, by omega⟩, -15001600), (⟨9, by omega⟩, -819200), (⟨13, by omega⟩, -163840), (⟨21, by omega⟩, -163840), (⟨29, by omega⟩, -163840), (⟨33, by omega⟩, -15001600), (⟨37, by omega⟩, -819200), (⟨42, by omega⟩, -819200), (⟨46, by omega⟩, -15001600), (⟨50, by omega⟩, -819200), (⟨61, by omega⟩, -15001600), (⟨74, by omega⟩, -819200), (⟨77, by omega⟩, -15001600), (⟨82, by omega⟩, -819200), (⟨86, by omega⟩, -15001600), (⟨90, by omega⟩, -30003200), (⟨94, by omega⟩, -30003200)]
  nu := [(⟨0, by omega⟩, -15001600), (⟨3, by omega⟩, 15001600), (⟨4, by omega⟩, 15001600), (⟨5, by omega⟩, -819200), (⟨10, by omega⟩, -15001600), (⟨11, by omega⟩, 163840), (⟨12, by omega⟩, 15001600), (⟨13, by omega⟩, 15001600), (⟨14, by omega⟩, 15001600), (⟨15, by omega⟩, -163840), (⟨16, by omega⟩, -163840), (⟨17, by omega⟩, -163840), (⟨18, by omega⟩, -15001600), (⟨19, by omega⟩, -15001600), (⟨20, by omega⟩, -15001600), (⟨21, by omega⟩, 15001600), (⟨22, by omega⟩, 15001600), (⟨23, by omega⟩, 15001600), (⟨25, by omega⟩, -15001600), (⟨26, by omega⟩, -15001600), (⟨28, by omega⟩, -15001600), (⟨30, by omega⟩, -16640000), (⟨31, by omega⟩, 1638400), (⟨32, by omega⟩, 1638400), (⟨33, by omega⟩, 15820800), (⟨34, by omega⟩, 15820800), (⟨35, by omega⟩, -819200), (⟨36, by omega⟩, -819200), (⟨37, by omega⟩, -819200), (⟨38, by omega⟩, -819200), (⟨39, by omega⟩, -819200), (⟨40, by omega⟩, -15001600), (⟨41, by omega⟩, -15001600)]
  claimed := 2067982979518955520000
}
def branch_box_3328 : RatBox 8 := { lower := box_3328.profileLo, upper := box_3328.profileHi }
def accepted_3328 : Bool := checkAt 527 1000 box_3328 cert_3328

def box_3329 : Box := { S := 1319203200, lo := ![0, 950238555, 65960160, 972912360, 1286223120, 0, 1286223120, 0], hi := ![16490040, 972912360, 98940240, 995586165, 1302713160, 16490040, 1319203200, 32980080] }
def cert_3329 : Certificate := {
  mu := [(⟨5, by omega⟩, -748204800), (⟨6, by omega⟩, -570998400), (⟨9, by omega⟩, -748204800), (⟨13, by omega⟩, -142515200), (⟨21, by omega⟩, -748204800), (⟨33, by omega⟩, -570998400), (⟨37, by omega⟩, -748204800), (⟨42, by omega⟩, -748204800), (⟨50, by omega⟩, -62361600), (⟨61, by omega⟩, -748204800), (⟨74, by omega⟩, -748204800), (⟨78, by omega⟩, -570998400), (⟨82, by omega⟩, -62361600), (⟨90, by omega⟩, -1141996800)]
  nu := [(⟨0, by omega⟩, -570998400), (⟨3, by omega⟩, 570998400), (⟨4, by omega⟩, 570998400), (⟨5, by omega⟩, -748204800), (⟨10, by omega⟩, -570998400), (⟨11, by omega⟩, 142515200), (⟨12, by omega⟩, 570998400), (⟨13, by omega⟩, 570998400), (⟨15, by omega⟩, -142515200), (⟨16, by omega⟩, -748204800), (⟨18, by omega⟩, -570998400), (⟨20, by omega⟩, -570998400), (⟨21, by omega⟩, 570998400), (⟨22, by omega⟩, 570998400), (⟨25, by omega⟩, -570998400), (⟨28, by omega⟩, -748204800), (⟨30, by omega⟩, -1381564800), (⟨31, by omega⟩, 810566400), (⟨32, by omega⟩, 810566400), (⟨33, by omega⟩, 1319203200), (⟨34, by omega⟩, 633360000), (⟨35, by omega⟩, -748204800), (⟨36, by omega⟩, -748204800), (⟨37, by omega⟩, -62361600), (⟨38, by omega⟩, -748204800), (⟨39, by omega⟩, -62361600), (⟨40, by omega⟩, -570998400)]
  claimed := 1209142066581639163975680000
}
def branch_box_3329 : RatBox 8 := { lower := box_3329.profileLo, upper := box_3329.profileHi }
def accepted_3329 : Bool := checkAt 527 1000 box_3329 cert_3329

def box_3332 : Box := { S := 25600, lo := ![0, 18660, 1280, 18880, 25280, 0, 24960, 0], hi := ![320, 18880, 1920, 19320, 25600, 320, 25600, 640] }
def cert_3332 : Certificate := {
  mu := [(⟨4, by omega⟩, -640), (⟨6, by omega⟩, -25600), (⟨13, by omega⟩, -25600), (⟨29, by omega⟩, -25600), (⟨33, by omega⟩, -25600), (⟨85, by omega⟩, -25600), (⟨90, by omega⟩, -51200), (⟨93, by omega⟩, -425600)]
  nu := [(⟨0, by omega⟩, -25600), (⟨3, by omega⟩, 25600), (⟨4, by omega⟩, 25600), (⟨10, by omega⟩, -25600), (⟨11, by omega⟩, 25600), (⟨12, by omega⟩, 25600), (⟨14, by omega⟩, 25600), (⟨15, by omega⟩, -25600), (⟨17, by omega⟩, -25600), (⟨19, by omega⟩, -25600), (⟨20, by omega⟩, -25600), (⟨21, by omega⟩, 25600), (⟨22, by omega⟩, 25600), (⟨25, by omega⟩, -25600), (⟨30, by omega⟩, -25600), (⟨33, by omega⟩, 25600), (⟨34, by omega⟩, 25600), (⟨40, by omega⟩, -25600)]
  claimed := 8730050560000
}
def branch_box_3332 : RatBox 8 := { lower := box_3332.profileLo, upper := box_3332.profileHi }
def accepted_3332 : Bool := checkAt 527 1000 box_3332 cert_3332

def box_3334 : Box := { S := 360960, lo := ![0, 260004, 18048, 269310, 356448, 0, 351936, 0], hi := ![4512, 263106, 27072, 272412, 360960, 4512, 360960, 9024] }
def cert_3334 : Certificate := {
  mu := [(⟨4, by omega⟩, -9024), (⟨6, by omega⟩, -360960), (⟨33, by omega⟩, -360960), (⟨78, by omega⟩, -360960), (⟨85, by omega⟩, -40960), (⟨90, by omega⟩, -721920), (⟨93, by omega⟩, -81920)]
  nu := [(⟨0, by omega⟩, -360960), (⟨3, by omega⟩, 360960), (⟨4, by omega⟩, 360960), (⟨10, by omega⟩, -360960), (⟨12, by omega⟩, 360960), (⟨13, by omega⟩, 360960), (⟨14, by omega⟩, 40960), (⟨18, by omega⟩, -360960), (⟨19, by omega⟩, -40960), (⟨20, by omega⟩, -360960), (⟨21, by omega⟩, 360960), (⟨22, by omega⟩, 360960), (⟨25, by omega⟩, -360960), (⟨30, by omega⟩, -360960), (⟨33, by omega⟩, 360960), (⟨34, by omega⟩, 360960), (⟨40, by omega⟩, -360960), (⟨41, by omega⟩, -40960)]
  claimed := 24452052752793600
}
def branch_box_3334 : RatBox 8 := { lower := box_3334.profileLo, upper := box_3334.profileHi }
def accepted_3334 : Bool := checkAt 527 1000 box_3334 cert_3334

def box_3336 : Box := { S := 228036480, lo := ![5700912, 160338150, 17102736, 168176904, 216634656, 0, 216634656, 0], hi := ![11401824, 168176904, 22803648, 176015658, 228036480, 11401824, 228036480, 11401824] }
def cert_3336 : Certificate := {
  mu := [(⟨5, by omega⟩, -126877440), (⟨6, by omega⟩, -101159040), (⟨9, by omega⟩, -126877440), (⟨14, by omega⟩, -101159040), (⟨22, by omega⟩, -69214080), (⟨30, by omega⟩, -31944960), (⟨33, by omega⟩, -101159040), (⟨37, by omega⟩, -126877440), (⟨42, by omega⟩, -22958080), (⟨70, by omega⟩, -101159040), (⟨74, by omega⟩, -22958080), (⟨78, by omega⟩, -69214080), (⟨86, by omega⟩, -31944960), (⟨89, by omega⟩, -202318080), (⟨94, by omega⟩, -51436800)]
  nu := [(⟨0, by omega⟩, -101159040), (⟨3, by omega⟩, 101159040), (⟨4, by omega⟩, 101159040), (⟨5, by omega⟩, -126877440), (⟨10, by omega⟩, -101159040), (⟨11, by omega⟩, 101159040), (⟨12, by omega⟩, 101159040), (⟨13, by omega⟩, 69214080), (⟨14, by omega⟩, 31944960), (⟨15, by omega⟩, -101159040), (⟨16, by omega⟩, -69214080), (⟨17, by omega⟩, -31944960), (⟨18, by omega⟩, -69214080), (⟨19, by omega⟩, -31944960), (⟨20, by omega⟩, -101159040), (⟨21, by omega⟩, 101159040), (⟨22, by omega⟩, 101159040), (⟨25, by omega⟩, -101159040), (⟨29, by omega⟩, -101159040), (⟨30, by omega⟩, -124117120), (⟨31, by omega⟩, 22958080), (⟨32, by omega⟩, 22958080), (⟨33, by omega⟩, 124117120), (⟨34, by omega⟩, 101159040), (⟨35, by omega⟩, -126877440), (⟨36, by omega⟩, -22958080), (⟨38, by omega⟩, -22958080), (⟨40, by omega⟩, -101159040), (⟨41, by omega⟩, -25718400)]
  claimed := 6224496902685458985369600
}
def branch_box_3336 : RatBox 8 := { lower := box_3336.profileLo, upper := box_3336.profileHi }
def accepted_3336 : Bool := checkAt 527 1000 box_3336 cert_3336

def box_3338 : Box := { S := 422912000, lo := ![10572800, 297360000, 21145600, 311897600, 401766400, 10572800, 401766400, 0], hi := ![21145600, 311897600, 31718400, 326435200, 422912000, 21145600, 422912000, 21145600] }
def cert_3338 : Certificate := {
  mu := [(⟨4, by omega⟩, -92507280), (⟨5, by omega⟩, -209945600), (⟨6, by omega⟩, -212966400), (⟨9, by omega⟩, -209945600), (⟨13, by omega⟩, -212966400), (⟨21, by omega⟩, -212966400), (⟨30, by omega⟩, -212966400), (⟨33, by omega⟩, -212966400), (⟨37, by omega⟩, -209945600), (⟨42, by omega⟩, -209945600), (⟨45, by omega⟩, -212966400), (⟨54, by omega⟩, -212966400), (⟨61, by omega⟩, -212966400), (⟨70, by omega⟩, -212966400), (⟨74, by omega⟩, -209945600), (⟨78, by omega⟩, -212966400), (⟨79, by omega⟩, -96556800), (⟨86, by omega⟩, -212966400), (⟨90, by omega⟩, -425932800), (⟨94, by omega⟩, -425932800)]
  nu := [(⟨0, by omega⟩, -212966400), (⟨3, by omega⟩, 212966400), (⟨4, by omega⟩, 212966400), (⟨5, by omega⟩, -209945600), (⟨10, by omega⟩, -212966400), (⟨11, by omega⟩, 212966400), (⟨12, by omega⟩, 212966400), (⟨13, by omega⟩, 212966400), (⟨14, by omega⟩, 212966400), (⟨15, by omega⟩, -212966400), (⟨16, by omega⟩, -212966400), (⟨17, by omega⟩, -212966400), (⟨18, by omega⟩, -212966400), (⟨19, by omega⟩, -212966400), (⟨20, by omega⟩, -212966400), (⟨21, by omega⟩, 212966400), (⟨22, by omega⟩, 212966400), (⟨23, by omega⟩, 212966400), (⟨24, by omega⟩, 212966400), (⟨25, by omega⟩, -212966400), (⟨26, by omega⟩, -212966400), (⟨27, by omega⟩, -212966400), (⟨28, by omega⟩, -212966400), (⟨29, by omega⟩, -212966400), (⟨30, by omega⟩, -422912000), (⟨31, by omega⟩, 209945600), (⟨32, by omega⟩, 113388800), (⟨33, by omega⟩, 422912000), (⟨34, by omega⟩, 212966400), (⟨35, by omega⟩, -209945600), (⟨36, by omega⟩, -209945600), (⟨38, by omega⟩, -209945600), (⟨39, by omega⟩, 96556800), (⟨40, by omega⟩, -212966400), (⟨41, by omega⟩, -212966400)]
  claimed := 39134880586852728832000000
}
def branch_box_3338 : RatBox 8 := { lower := box_3338.profileLo, upper := box_3338.profileHi }
def accepted_3338 : Bool := checkAt 527 1000 box_3338 cert_3338

def box_3340 : Box := { S := 30004800, lo := ![750120, 21097125, 1500240, 22128540, 28504560, 0, 28504560, 750120], hi := ![1500240, 22128540, 2250360, 23159955, 30004800, 750120, 30004800, 1500240] }
def cert_3340 : Certificate := {
  mu := [(⟨5, by omega⟩, -16694400), (⟨6, by omega⟩, -13310400), (⟨9, by omega⟩, -16694400), (⟨13, by omega⟩, -13310400), (⟨29, by omega⟩, -13310400), (⟨33, by omega⟩, -13310400), (⟨37, by omega⟩, -16694400), (⟨42, by omega⟩, -3020800), (⟨45, by omega⟩, -13310400), (⟨53, by omega⟩, -13310400), (⟨61, by omega⟩, -13310400), (⟨69, by omega⟩, -13310400), (⟨74, by omega⟩, -3020800), (⟨85, by omega⟩, -13310400), (⟨89, by omega⟩, -26620800), (⟨93, by omega⟩, -26620800)]
  nu := [(⟨0, by omega⟩, -13310400), (⟨3, by omega⟩, 13310400), (⟨4, by omega⟩, 13310400), (⟨5, by omega⟩, -16694400), (⟨10, by omega⟩, -13310400), (⟨11, by omega⟩, 13310400), (⟨12, by omega⟩, 13310400), (⟨14, by omega⟩, 13310400), (⟨15, by omega⟩, -13310400), (⟨17, by omega⟩, -13310400), (⟨19, by omega⟩, -13310400), (⟨20, by omega⟩, -13310400), (⟨21, by omega⟩, 13310400), (⟨22, by omega⟩, 13310400), (⟨23, by omega⟩, 13310400), (⟨24, by omega⟩, 13310400), (⟨25, by omega⟩, -13310400), (⟨26, by omega⟩, -13310400), (⟨27, by omega⟩, -13310400), (⟨28, by omega⟩, -13310400), (⟨29, by omega⟩, -13310400), (⟨30, by omega⟩, -16331200), (⟨31, by omega⟩, 3020800), (⟨32, by omega⟩, 3020800), (⟨33, by omega⟩, 16331200), (⟨34, by omega⟩, 13310400), (⟨35, by omega⟩, -16694400), (⟨36, by omega⟩, -3020800), (⟨38, by omega⟩, -3020800), (⟨40, by omega⟩, -13310400), (⟨41, by omega⟩, -13310400)]
  claimed := 14114018802291287040000
}
def branch_box_3340 : RatBox 8 := { lower := box_3340.profileLo, upper := box_3340.profileHi }
def accepted_3340 : Bool := checkAt 527 1000 box_3340 cert_3340

def box_3341 : Box := { S := 22108800, lo := ![552720, 15545250, 1105440, 16305240, 21003360, 0, 21003360, 0], hi := ![1105440, 16305240, 1658160, 17065230, 21556080, 552720, 22108800, 552720] }
def cert_3341 : Certificate := {
  mu := [(⟨5, by omega⟩, -12633600), (⟨6, by omega⟩, -9475200), (⟨9, by omega⟩, -12633600), (⟨14, by omega⟩, -9475200), (⟨22, by omega⟩, -12633600), (⟨33, by omega⟩, -9475200), (⟨37, by omega⟩, -12633600), (⟨42, by omega⟩, -12633600), (⟨45, by omega⟩, -4812800), (⟨50, by omega⟩, -2150400), (⟨61, by omega⟩, -12633600), (⟨74, by omega⟩, -12633600), (⟨82, by omega⟩, -2150400), (⟨90, by omega⟩, -18950400)]
  nu := [(⟨0, by omega⟩, -9475200), (⟨3, by omega⟩, 9475200), (⟨4, by omega⟩, 9475200), (⟨5, by omega⟩, -12633600), (⟨10, by omega⟩, -9475200), (⟨11, by omega⟩, 9475200), (⟨12, by omega⟩, 9475200), (⟨15, by omega⟩, -9475200), (⟨16, by omega⟩, -12633600), (⟨20, by omega⟩, -9475200), (⟨21, by omega⟩, 9475200), (⟨22, by omega⟩, 9475200), (⟨23, by omega⟩, 4812800), (⟨25, by omega⟩, -9475200), (⟨26, by omega⟩, -4812800), (⟨28, by omega⟩, -12633600), (⟨30, by omega⟩, -24259200), (⟨31, by omega⟩, 14784000), (⟨32, by omega⟩, 14784000), (⟨33, by omega⟩, 22108800), (⟨34, by omega⟩, 11625600), (⟨35, by omega⟩, -12633600), (⟨36, by omega⟩, -12633600), (⟨37, by omega⟩, -2150400), (⟨38, by omega⟩, -12633600), (⟨39, by omega⟩, -2150400), (⟨40, by omega⟩, -9475200)]
  claimed := 5633506177504450560000
}
def branch_box_3341 : RatBox 8 := { lower := box_3341.profileLo, upper := box_3341.profileHi }
def accepted_3341 : Bool := checkAt 527 1000 box_3341 cert_3341

def box_3343 : Box := { S := 209600, lo := ![5240, 147375, 10480, 154580, 204360, 0, 199120, 0], hi := ![10480, 154580, 15720, 161785, 209600, 5240, 204360, 5240] }
def cert_3343 : Certificate := {
  mu := [(⟨4, by omega⟩, -44175), (⟨5, by omega⟩, -118400), (⟨6, by omega⟩, -91200), (⟨9, by omega⟩, -118400), (⟨14, by omega⟩, -91200), (⟨22, by omega⟩, -27200), (⟨30, by omega⟩, -91200), (⟨33, by omega⟩, -91200), (⟨37, by omega⟩, -118400), (⟨42, by omega⟩, -113088), (⟨50, by omega⟩, -118400), (⟨54, by omega⟩, -91200), (⟨61, by omega⟩, -27200), (⟨70, by omega⟩, -91200), (⟨74, by omega⟩, -113088), (⟨82, by omega⟩, -118400), (⟨86, by omega⟩, -91200), (⟨90, by omega⟩, -226176)]
  nu := [(⟨0, by omega⟩, -113088), (⟨3, by omega⟩, 113088), (⟨4, by omega⟩, 113088), (⟨5, by omega⟩, -118400), (⟨10, by omega⟩, -91200), (⟨11, by omega⟩, 91200), (⟨12, by omega⟩, 91200), (⟨14, by omega⟩, 91200), (⟨15, by omega⟩, -91200), (⟨16, by omega⟩, -27200), (⟨17, by omega⟩, -91200), (⟨19, by omega⟩, -91200), (⟨20, by omega⟩, -91200), (⟨21, by omega⟩, 91200), (⟨22, by omega⟩, 91200), (⟨24, by omega⟩, 91200), (⟨25, by omega⟩, -91200), (⟨27, by omega⟩, -91200), (⟨28, by omega⟩, -27200), (⟨29, by omega⟩, -91200), (⟨30, by omega⟩, -344576), (⟨31, by omega⟩, 231488), (⟨32, by omega⟩, 231488), (⟨33, by omega⟩, 226176), (⟨34, by omega⟩, 231488), (⟨35, by omega⟩, -118400), (⟨36, by omega⟩, -113088), (⟨37, by omega⟩, -118400), (⟨38, by omega⟩, -113088), (⟨39, by omega⟩, -118400), (⟨40, by omega⟩, -113088)]
  claimed := 4753415779840000
}
def branch_box_3343 : RatBox 8 := { lower := box_3343.profileLo, upper := box_3343.profileHi }
def accepted_3343 : Bool := checkAt 527 1000 box_3343 cert_3343

def box_3346 : Box := { S := 75148800, lo := ![1878720, 54130620, 3757440, 55422240, 73270080, 0, 73270080, 0], hi := ![3757440, 55422240, 5636160, 58005480, 75148800, 1878720, 75148800, 1878720] }
def cert_3346 : Certificate := {
  mu := [(⟨4, by omega⟩, -1781440), (⟨5, by omega⟩, -3891200), (⟨6, by omega⟩, -71257600), (⟨9, by omega⟩, -3891200), (⟨13, by omega⟩, -71257600), (⟨30, by omega⟩, -7500800), (⟨33, by omega⟩, -71257600), (⟨37, by omega⟩, -3891200), (⟨42, by omega⟩, -3891200), (⟨50, by omega⟩, -3891200), (⟨61, by omega⟩, -3891200), (⟨74, by omega⟩, -3891200), (⟨82, by omega⟩, -3891200), (⟨86, by omega⟩, -7500800), (⟨90, by omega⟩, -142515200)]
  nu := [(⟨0, by omega⟩, -71257600), (⟨3, by omega⟩, 71257600), (⟨4, by omega⟩, 71257600), (⟨5, by omega⟩, -3891200), (⟨10, by omega⟩, -71257600), (⟨11, by omega⟩, 71257600), (⟨12, by omega⟩, 71257600), (⟨14, by omega⟩, 7500800), (⟨15, by omega⟩, -71257600), (⟨17, by omega⟩, -7500800), (⟨19, by omega⟩, -7500800), (⟨20, by omega⟩, -71257600), (⟨21, by omega⟩, 71257600), (⟨22, by omega⟩, 71257600), (⟨25, by omega⟩, -71257600), (⟨28, by omega⟩, -3891200), (⟨30, by omega⟩, -79040000), (⟨31, by omega⟩, 7782400), (⟨32, by omega⟩, 7782400), (⟨33, by omega⟩, 75148800), (⟨34, by omega⟩, 75148800), (⟨35, by omega⟩, -3891200), (⟨36, by omega⟩, -3891200), (⟨37, by omega⟩, -3891200), (⟨38, by omega⟩, -3891200), (⟨39, by omega⟩, -3891200), (⟨40, by omega⟩, -71257600)]
  claimed := 221617783613182279680000
}
def branch_box_3346 : RatBox 8 := { lower := box_3346.profileLo, upper := box_3346.profileHi }
def accepted_3346 : Bool := checkAt 527 1000 box_3346 cert_3346

def box_3348 : Box := { S := 1241932800, lo := ![31048320, 873234000, 62096640, 937271160, 1210884480, 0, 1210884480, 0], hi := ![62096640, 894579720, 93144960, 958616880, 1241932800, 31048320, 1241932800, 31048320] }
def cert_3348 : Certificate := {
  mu := [(⟨5, by omega⟩, -64307200), (⟨6, by omega⟩, -1177625600), (⟨9, by omega⟩, -64307200), (⟨13, by omega⟩, -1177625600), (⟨22, by omega⟩, -64307200), (⟨33, by omega⟩, -1177625600), (⟨37, by omega⟩, -64307200), (⟨42, by omega⟩, -64307200), (⟨50, by omega⟩, -64307200), (⟨54, by omega⟩, -64307200), (⟨69, by omega⟩, -64307200), (⟨74, by omega⟩, -64307200), (⟨78, by omega⟩, -6553600), (⟨82, by omega⟩, -64307200), (⟨89, by omega⟩, -1177625600), (⟨90, by omega⟩, -1177625600)]
  nu := [(⟨0, by omega⟩, -1177625600), (⟨3, by omega⟩, 1177625600), (⟨4, by omega⟩, 1177625600), (⟨5, by omega⟩, -64307200), (⟨10, by omega⟩, -1177625600), (⟨11, by omega⟩, 1177625600), (⟨12, by omega⟩, 1177625600), (⟨13, by omega⟩, 6553600), (⟨15, by omega⟩, -1177625600), (⟨16, by omega⟩, -64307200), (⟨18, by omega⟩, -6553600), (⟨20, by omega⟩, -1177625600), (⟨21, by omega⟩, 1177625600), (⟨22, by omega⟩, 1177625600), (⟨24, by omega⟩, 64307200), (⟨25, by omega⟩, -1177625600), (⟨27, by omega⟩, -64307200), (⟨29, by omega⟩, -64307200), (⟨30, by omega⟩, -1306240000), (⟨31, by omega⟩, 128614400), (⟨32, by omega⟩, 128614400), (⟨33, by omega⟩, 1241932800), (⟨34, by omega⟩, 1241932800), (⟨35, by omega⟩, -64307200), (⟨36, by omega⟩, -64307200), (⟨37, by omega⟩, -64307200), (⟨38, by omega⟩, -64307200), (⟨39, by omega⟩, -64307200), (⟨40, by omega⟩, -1177625600)]
  claimed := 999466639873288708423680000
}
def branch_box_3348 : RatBox 8 := { lower := box_3348.profileLo, upper := box_3348.profileHi }
def accepted_3348 : Bool := checkAt 527 1000 box_3348 cert_3348

end PeaceableQueens.UpperBound.Generated.Even.Core
