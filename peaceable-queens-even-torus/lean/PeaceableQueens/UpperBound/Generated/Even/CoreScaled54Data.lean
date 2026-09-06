import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_2702 : Box := { S := 98172928000, lo := ![0, 69449676800, 0, 75355392000, 95718604800, 0, 96945766400, 0], hi := ![2454323200, 69871513600, 4908646400, 75777228800, 96945766400, 1227161600, 98172928000, 2454323200] }
def cert_2702 : Certificate := {
  mu := [(⟨5, by omega⟩, -4908646400), (⟨6, by omega⟩, -93264281600), (⟨9, by omega⟩, -4908646400), (⟨21, by omega⟩, -4908646400), (⟨34, by omega⟩, -629145600), (⟨37, by omega⟩, -4908646400), (⟨42, by omega⟩, -4908646400), (⟨46, by omega⟩, -419430400), (⟨50, by omega⟩, -4908646400), (⟨62, by omega⟩, -4908646400), (⟨74, by omega⟩, -4908646400), (⟨82, by omega⟩, -4908646400), (⟨89, by omega⟩, -186528563200)]
  nu := [(⟨0, by omega⟩, -93264281600), (⟨3, by omega⟩, 93264281600), (⟨4, by omega⟩, 93264281600), (⟨5, by omega⟩, -4908646400), (⟨10, by omega⟩, -93264281600), (⟨12, by omega⟩, 93264281600), (⟨16, by omega⟩, -4908646400), (⟨20, by omega⟩, -93264281600), (⟨21, by omega⟩, 93264281600), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -4908646400), (⟨30, by omega⟩, -103081574400), (⟨31, by omega⟩, 9817292800), (⟨32, by omega⟩, 9817292800), (⟨33, by omega⟩, 98172928000), (⟨34, by omega⟩, 98172928000), (⟨35, by omega⟩, -4908646400), (⟨36, by omega⟩, -4908646400), (⟨37, by omega⟩, -4908646400), (⟨38, by omega⟩, -4908646400), (⟨39, by omega⟩, -4908646400), (⟨40, by omega⟩, -93264281600)]
  claimed := 497316919591503762405982208000000
}
def branch_box_2702 : RatBox 8 := { lower := box_2702.profileLo, upper := box_2702.profileHi }
def accepted_2702 : Bool := checkAt 527 1000 box_2702 cert_2702

def box_2704 : Box := { S := 407076864000, lo := ![0, 289724236800, 0, 310714137600, 396899942400, 0, 401988403200, 0], hi := ![10176921600, 293222553600, 20353843200, 314212454400, 401988403200, 5088460800, 407076864000, 10176921600] }
def cert_2704 : Certificate := {
  mu := [(⟨5, by omega⟩, -20353843200), (⟨6, by omega⟩, -386723020800), (⟨9, by omega⟩, -20353843200), (⟨13, by omega⟩, -1074790400), (⟨22, by omega⟩, -20353843200), (⟨34, by omega⟩, -2647654400), (⟨37, by omega⟩, -20353843200), (⟨42, by omega⟩, -20353843200), (⟨50, by omega⟩, -20353843200), (⟨62, by omega⟩, -20353843200), (⟨74, by omega⟩, -20353843200), (⟨82, by omega⟩, -20353843200), (⟨89, by omega⟩, -773446041600)]
  nu := [(⟨0, by omega⟩, -386723020800), (⟨3, by omega⟩, 386723020800), (⟨4, by omega⟩, 386723020800), (⟨5, by omega⟩, -20353843200), (⟨10, by omega⟩, -386723020800), (⟨11, by omega⟩, 1074790400), (⟨12, by omega⟩, 386723020800), (⟨15, by omega⟩, -1074790400), (⟨16, by omega⟩, -20353843200), (⟨20, by omega⟩, -386723020800), (⟨21, by omega⟩, 386723020800), (⟨22, by omega⟩, 2647654400), (⟨25, by omega⟩, -2647654400), (⟨28, by omega⟩, -20353843200), (⟨30, by omega⟩, -427430707200), (⟨31, by omega⟩, 40707686400), (⟨32, by omega⟩, 40707686400), (⟨33, by omega⟩, 407076864000), (⟨34, by omega⟩, 407076864000), (⟨35, by omega⟩, -20353843200), (⟨36, by omega⟩, -20353843200), (⟨37, by omega⟩, -20353843200), (⟨38, by omega⟩, -20353843200), (⟨39, by omega⟩, -20353843200), (⟨40, by omega⟩, -386723020800)]
  claimed := 35456607483344302583234691072000000
}
def branch_box_2704 : RatBox 8 := { lower := box_2704.profileLo, upper := box_2704.profileHi }
def accepted_2704 : Bool := checkAt 527 1000 box_2704 cert_2704

def box_2708 : Box := { S := 12800, lo := ![0, 9165, 0, 9715, 12480, 0, 12640, 0], hi := ![320, 9220, 640, 9770, 12640, 160, 12800, 320] }
def cert_2708 : Certificate := {
  mu := [(⟨6, by omega⟩, -12800), (⟨89, by omega⟩, -25600)]
  nu := [(⟨0, by omega⟩, -12800), (⟨3, by omega⟩, 12800), (⟨4, by omega⟩, 12800), (⟨10, by omega⟩, -12800), (⟨12, by omega⟩, 12800), (⟨20, by omega⟩, -12800), (⟨21, by omega⟩, 12800), (⟨30, by omega⟩, -12800), (⟨33, by omega⟩, 12800), (⟨34, by omega⟩, 12800), (⟨40, by omega⟩, -12800)]
  claimed := 1102315520000
}
def branch_box_2708 : RatBox 8 := { lower := box_2708.profileLo, upper := box_2708.profileHi }
def accepted_2708 : Bool := checkAt 527 1000 box_2708 cert_2708

def box_2716 : Box := { S := 9587200, lo := ![0, 6782195, 0, 7358925, 9467360, 0, 9347520, 0], hi := ![239680, 6823390, 479360, 7400120, 9587200, 119840, 9587200, 239680] }
def cert_2716 : Certificate := {
  mu := [(⟨4, by omega⟩, -239680), (⟨6, by omega⟩, -9587200), (⟨54, by omega⟩, -819200), (⟨90, by omega⟩, -19174400)]
  nu := [(⟨0, by omega⟩, -9587200), (⟨3, by omega⟩, 9587200), (⟨4, by omega⟩, 9587200), (⟨10, by omega⟩, -9587200), (⟨12, by omega⟩, 9587200), (⟨20, by omega⟩, -9587200), (⟨21, by omega⟩, 9587200), (⟨24, by omega⟩, 819200), (⟨27, by omega⟩, -819200), (⟨30, by omega⟩, -9587200), (⟨33, by omega⟩, 9587200), (⟨34, by omega⟩, 9587200), (⟨40, by omega⟩, -9587200)]
  claimed := 462906306113699840000
}
def branch_box_2716 : RatBox 8 := { lower := box_2716.profileLo, upper := box_2716.profileHi }
def accepted_2716 : Bool := checkAt 527 1000 box_2716 cert_2716

def box_2718 : Box := { S := 2361600, lo := ![0, 1680795, 0, 1802565, 2332080, 0, 2302560, 0], hi := ![59040, 1701090, 118080, 1822860, 2361600, 29520, 2361600, 59040] }
def cert_2718 : Certificate := {
  mu := [(⟨4, by omega⟩, -59040), (⟨6, by omega⟩, -2361600), (⟨54, by omega⟩, -204800), (⟨90, by omega⟩, -4723200)]
  nu := [(⟨0, by omega⟩, -2361600), (⟨3, by omega⟩, 2361600), (⟨4, by omega⟩, 2361600), (⟨10, by omega⟩, -2361600), (⟨12, by omega⟩, 2361600), (⟨20, by omega⟩, -2361600), (⟨21, by omega⟩, 2361600), (⟨24, by omega⟩, 204800), (⟨27, by omega⟩, -204800), (⟨30, by omega⟩, -2361600), (⟨33, by omega⟩, 2361600), (⟨34, by omega⟩, 2361600), (⟨40, by omega⟩, -2361600)]
  claimed := 6918895249735680000
}
def branch_box_2718 : RatBox 8 := { lower := box_2718.profileLo, upper := box_2718.profileHi }
def accepted_2718 : Bool := checkAt 527 1000 box_2718 cert_2718

def box_2722 : Box := { S := 9305600, lo := ![0, 6662955, 0, 7062805, 9189280, 0, 9072960, 0], hi := ![232640, 6702940, 465280, 7102790, 9305600, 116320, 9305600, 232640] }
def cert_2722 : Certificate := {
  mu := [(⟨4, by omega⟩, -232640), (⟨6, by omega⟩, -9305600), (⟨54, by omega⟩, -819200), (⟨90, by omega⟩, -18611200)]
  nu := [(⟨0, by omega⟩, -9305600), (⟨3, by omega⟩, 9305600), (⟨4, by omega⟩, 9305600), (⟨10, by omega⟩, -9305600), (⟨12, by omega⟩, 9305600), (⟨20, by omega⟩, -9305600), (⟨21, by omega⟩, 9305600), (⟨24, by omega⟩, 819200), (⟨27, by omega⟩, -819200), (⟨30, by omega⟩, -9305600), (⟨33, by omega⟩, 9305600), (⟨34, by omega⟩, 9305600), (⟨40, by omega⟩, -9305600)]
  claimed := 423302542146273280000
}
def branch_box_2722 : RatBox 8 := { lower := box_2722.profileLo, upper := box_2722.profileHi }
def accepted_2722 : Bool := checkAt 527 1000 box_2722 cert_2722

def box_2727 : Box := { S := 27929600, lo := ![0, 19638000, 0, 21078120, 27231360, 349120, 27231360, 0], hi := ![698240, 20118040, 1396480, 21558160, 27580480, 698240, 27580480, 349120] }
def cert_2727 : Certificate := {
  mu := [(⟨4, by omega⟩, -6183080), (⟨5, by omega⟩, -15974400), (⟨6, by omega⟩, -11955200), (⟨9, by omega⟩, -15974400), (⟨13, by omega⟩, -11955200), (⟨21, by omega⟩, -11955200), (⟨30, by omega⟩, -11955200), (⟨33, by omega⟩, -11955200), (⟨37, by omega⟩, -15974400), (⟨42, by omega⟩, -15974400), (⟨45, by omega⟩, -11955200), (⟨50, by omega⟩, -15974400), (⟨54, by omega⟩, -11955200), (⟨61, by omega⟩, -11955200), (⟨70, by omega⟩, -11955200), (⟨74, by omega⟩, -15974400), (⟨77, by omega⟩, -11955200), (⟨82, by omega⟩, -15974400), (⟨86, by omega⟩, -11955200), (⟨90, by omega⟩, -31948800), (⟨94, by omega⟩, -23910400)]
  nu := [(⟨0, by omega⟩, -15974400), (⟨3, by omega⟩, 15974400), (⟨4, by omega⟩, 15974400), (⟨5, by omega⟩, -15974400), (⟨10, by omega⟩, -11955200), (⟨11, by omega⟩, 11955200), (⟨12, by omega⟩, 11955200), (⟨13, by omega⟩, 11955200), (⟨14, by omega⟩, 11955200), (⟨15, by omega⟩, -11955200), (⟨16, by omega⟩, -11955200), (⟨17, by omega⟩, -11955200), (⟨18, by omega⟩, -11955200), (⟨19, by omega⟩, -11955200), (⟨20, by omega⟩, -11955200), (⟨21, by omega⟩, 11955200), (⟨22, by omega⟩, 11955200), (⟨23, by omega⟩, 11955200), (⟨24, by omega⟩, 11955200), (⟨25, by omega⟩, -11955200), (⟨26, by omega⟩, -11955200), (⟨27, by omega⟩, -11955200), (⟨28, by omega⟩, -11955200), (⟨29, by omega⟩, -11955200), (⟨30, by omega⟩, -47923200), (⟨31, by omega⟩, 31948800), (⟨32, by omega⟩, 31948800), (⟨33, by omega⟩, 31948800), (⟨34, by omega⟩, 31948800), (⟨35, by omega⟩, -15974400), (⟨36, by omega⟩, -15974400), (⟨37, by omega⟩, -15974400), (⟨38, by omega⟩, -15974400), (⟨39, by omega⟩, -15974400), (⟨40, by omega⟩, -15974400), (⟨41, by omega⟩, -11955200)]
  claimed := 11406431184759685120000
}
def branch_box_2727 : RatBox 8 := { lower := box_2727.profileLo, upper := box_2727.profileHi }
def accepted_2727 : Bool := checkAt 527 1000 box_2727 cert_2727

def box_2734 : Box := { S := 259891200, lo := ![0, 183852720, 0, 198370080, 253393920, 3248640, 256642560, 0], hi := ![6497280, 184969440, 12994560, 200603520, 256642560, 6497280, 259891200, 3248640] }
def cert_2734 : Certificate := {
  mu := [(⟨5, by omega⟩, -13107200), (⟨6, by omega⟩, -246784000), (⟨9, by omega⟩, -13107200), (⟨13, by omega⟩, -246784000), (⟨21, by omega⟩, -246784000), (⟨34, by omega⟩, -246784000), (⟨38, by omega⟩, -13107200), (⟨42, by omega⟩, -13107200), (⟨45, by omega⟩, -246784000), (⟨50, by omega⟩, -13107200), (⟨61, by omega⟩, -246784000), (⟨74, by omega⟩, -13107200), (⟨77, by omega⟩, -246784000), (⟨82, by omega⟩, -13107200), (⟨89, by omega⟩, -493568000)]
  nu := [(⟨0, by omega⟩, -246784000), (⟨3, by omega⟩, 246784000), (⟨4, by omega⟩, 246784000), (⟨5, by omega⟩, -13107200), (⟨10, by omega⟩, -246784000), (⟨11, by omega⟩, 246784000), (⟨12, by omega⟩, 246784000), (⟨13, by omega⟩, 246784000), (⟨15, by omega⟩, -246784000), (⟨16, by omega⟩, -246784000), (⟨18, by omega⟩, -246784000), (⟨20, by omega⟩, -246784000), (⟨21, by omega⟩, 246784000), (⟨22, by omega⟩, 246784000), (⟨23, by omega⟩, 246784000), (⟨25, by omega⟩, -246784000), (⟨26, by omega⟩, -246784000), (⟨28, by omega⟩, -246784000), (⟨30, by omega⟩, -272998400), (⟨31, by omega⟩, 26214400), (⟨32, by omega⟩, 26214400), (⟨33, by omega⟩, 259891200), (⟨34, by omega⟩, 259891200), (⟨35, by omega⟩, -13107200), (⟨36, by omega⟩, -13107200), (⟨37, by omega⟩, -13107200), (⟨38, by omega⟩, -13107200), (⟨39, by omega⟩, -13107200), (⟨40, by omega⟩, -246784000)]
  claimed := 9185197595011496017920000
}
def branch_box_2734 : RatBox 8 := { lower := box_2734.profileLo, upper := box_2734.profileHi }
def accepted_2734 : Bool := checkAt 527 1000 box_2734 cert_2734

def box_2736 : Box := { S := 6400, lo := ![0, 4555, 0, 4885, 6240, 80, 6320, 0], hi := ![160, 4610, 320, 4940, 6320, 160, 6400, 80] }
def cert_2736 : Certificate := {
  mu := [(⟨6, by omega⟩, -6400), (⟨45, by omega⟩, -6400), (⟨77, by omega⟩, -6400), (⟨89, by omega⟩, -12800)]
  nu := [(⟨0, by omega⟩, -6400), (⟨3, by omega⟩, 6400), (⟨4, by omega⟩, 6400), (⟨10, by omega⟩, -6400), (⟨12, by omega⟩, 6400), (⟨13, by omega⟩, 6400), (⟨18, by omega⟩, -6400), (⟨20, by omega⟩, -6400), (⟨21, by omega⟩, 6400), (⟨23, by omega⟩, 6400), (⟨26, by omega⟩, -6400), (⟨30, by omega⟩, -6400), (⟨33, by omega⟩, 6400), (⟨34, by omega⟩, 6400), (⟨40, by omega⟩, -6400)]
  claimed := 136069120000
}
def branch_box_2736 : RatBox 8 := { lower := box_2736.profileLo, upper := box_2736.profileHi }
def accepted_2736 : Bool := checkAt 527 1000 box_2736 cert_2736

def box_2738 : Box := { S := 205573939200, lo := ![0, 147194152560, 0, 155144082240, 200434590720, 2569674240, 203004264960, 0], hi := ![5139348480, 148077478080, 10278696960, 156910733280, 203004264960, 5139348480, 205573939200, 2569674240] }
def cert_2738 : Certificate := {
  mu := [(⟨5, by omega⟩, -10367795200), (⟨6, by omega⟩, -195206144000), (⟨10, by omega⟩, -10367795200), (⟨13, by omega⟩, -195206144000), (⟨21, by omega⟩, -195206144000), (⟨37, by omega⟩, -10367795200), (⟨42, by omega⟩, -10367795200), (⟨45, by omega⟩, -195206144000), (⟨50, by omega⟩, -10367795200), (⟨54, by omega⟩, -1677721600), (⟨69, by omega⟩, -8690073600), (⟨74, by omega⟩, -10367795200), (⟨77, by omega⟩, -195206144000), (⟨82, by omega⟩, -10367795200), (⟨89, by omega⟩, -390412288000), (⟨94, by omega⟩, -3355443200)]
  nu := [(⟨0, by omega⟩, -195206144000), (⟨3, by omega⟩, 195206144000), (⟨4, by omega⟩, 195206144000), (⟨5, by omega⟩, -10367795200), (⟨10, by omega⟩, -195206144000), (⟨11, by omega⟩, 195206144000), (⟨12, by omega⟩, 195206144000), (⟨13, by omega⟩, 195206144000), (⟨15, by omega⟩, -195206144000), (⟨16, by omega⟩, -195206144000), (⟨18, by omega⟩, -195206144000), (⟨20, by omega⟩, -195206144000), (⟨21, by omega⟩, 195206144000), (⟨23, by omega⟩, 195206144000), (⟨24, by omega⟩, 1677721600), (⟨26, by omega⟩, -195206144000), (⟨27, by omega⟩, -1677721600), (⟨29, by omega⟩, -8690073600), (⟨30, by omega⟩, -215941734400), (⟨31, by omega⟩, 20735590400), (⟨32, by omega⟩, 20735590400), (⟨33, by omega⟩, 205573939200), (⟨34, by omega⟩, 205573939200), (⟨35, by omega⟩, -10367795200), (⟨36, by omega⟩, -10367795200), (⟨37, by omega⟩, -10367795200), (⟨38, by omega⟩, -10367795200), (⟨39, by omega⟩, -10367795200), (⟨40, by omega⟩, -195206144000), (⟨41, by omega⟩, -1677721600)]
  claimed := 4546057832183431535745124270080000
}
def branch_box_2738 : RatBox 8 := { lower := box_2738.profileLo, upper := box_2738.profileHi }
def accepted_2738 : Bool := checkAt 527 1000 box_2738 cert_2738

def box_2740 : Box := { S := 8089600, lo := ![0, 5757520, 0, 6105120, 7988480, 101120, 7887360, 0], hi := ![202240, 5827040, 404480, 6244160, 8089600, 202240, 8089600, 101120] }
def cert_2740 : Certificate := {
  mu := [(⟨4, by omega⟩, -306520), (⟨6, by omega⟩, -8089600), (⟨34, by omega⟩, -8089600), (⟨45, by omega⟩, -8089600), (⟨54, by omega⟩, -8089600), (⟨61, by omega⟩, -8089600), (⟨70, by omega⟩, -8089600), (⟨77, by omega⟩, -8089600), (⟨86, by omega⟩, -8089600), (⟨90, by omega⟩, -16073600), (⟨94, by omega⟩, -320803200)]
  nu := [(⟨0, by omega⟩, -8089600), (⟨3, by omega⟩, 8036800), (⟨4, by omega⟩, 8089600), (⟨10, by omega⟩, -8089600), (⟨12, by omega⟩, 8089600), (⟨13, by omega⟩, 8089600), (⟨14, by omega⟩, 8089600), (⟨18, by omega⟩, -8089600), (⟨19, by omega⟩, -8089600), (⟨20, by omega⟩, -8089600), (⟨21, by omega⟩, 8089600), (⟨22, by omega⟩, 8089600), (⟨23, by omega⟩, 8089600), (⟨24, by omega⟩, 8089600), (⟨25, by omega⟩, -8089600), (⟨26, by omega⟩, -8089600), (⟨27, by omega⟩, -8089600), (⟨28, by omega⟩, -8089600), (⟨29, by omega⟩, -8089600), (⟨30, by omega⟩, -8089600), (⟨33, by omega⟩, 8036800), (⟨34, by omega⟩, 8089600), (⟨40, by omega⟩, -8036800), (⟨41, by omega⟩, -8089600)]
  claimed := 278951680519700480000
}
def branch_box_2740 : RatBox 8 := { lower := box_2740.profileLo, upper := box_2740.profileHi }
def accepted_2740 : Bool := checkAt 527 1000 box_2740 cert_2740

def box_2742 : Box := { S := 8089600, lo := ![0, 5688000, 0, 6174640, 7988480, 101120, 7887360, 0], hi := ![202240, 5757520, 404480, 6244160, 8089600, 202240, 8089600, 101120] }
def cert_2742 : Certificate := {
  mu := [(⟨4, by omega⟩, -271760), (⟨6, by omega⟩, -8089600), (⟨34, by omega⟩, -8089600), (⟨45, by omega⟩, -8089600), (⟨54, by omega⟩, -8089600), (⟨61, by omega⟩, -8089600), (⟨70, by omega⟩, -8089600), (⟨77, by omega⟩, -8089600), (⟨86, by omega⟩, -8089600), (⟨90, by omega⟩, -16108800), (⟨94, by omega⟩, -323584000)]
  nu := [(⟨0, by omega⟩, -8089600), (⟨3, by omega⟩, 8054400), (⟨4, by omega⟩, 8089600), (⟨10, by omega⟩, -8089600), (⟨12, by omega⟩, 8089600), (⟨13, by omega⟩, 8089600), (⟨14, by omega⟩, 8089600), (⟨18, by omega⟩, -8089600), (⟨19, by omega⟩, -8089600), (⟨20, by omega⟩, -8089600), (⟨21, by omega⟩, 8089600), (⟨22, by omega⟩, 8089600), (⟨23, by omega⟩, 8089600), (⟨24, by omega⟩, 8089600), (⟨25, by omega⟩, -8089600), (⟨26, by omega⟩, -8089600), (⟨27, by omega⟩, -8089600), (⟨28, by omega⟩, -8089600), (⟨29, by omega⟩, -8089600), (⟨30, by omega⟩, -8089600), (⟨33, by omega⟩, 8054400), (⟨34, by omega⟩, 8089600), (⟨40, by omega⟩, -8054400), (⟨41, by omega⟩, -8089600)]
  claimed := 278951680519700480000
}
def branch_box_2742 : RatBox 8 := { lower := box_2742.profileLo, upper := box_2742.profileHi }
def accepted_2742 : Bool := checkAt 527 1000 box_2742 cert_2742

def box_2743 : Box := { S := 1475564876800, lo := ![0, 1037506554000, 0, 1113590367960, 1438675754880, 18444560960, 1438675754880, 18444560960], hi := ![36889121920, 1062867825320, 73778243840, 1138951639280, 1457120315840, 36889121920, 1475564876800, 36889121920] }
def cert_2743 : Certificate := {
  mu := [(⟨5, by omega⟩, -837809356800), (⟨6, by omega⟩, -637755520000), (⟨9, by omega⟩, -837809356800), (⟨13, by omega⟩, -100026918400), (⟨21, by omega⟩, -100026918400), (⟨29, by omega⟩, -100026918400), (⟨33, by omega⟩, -83828940800), (⟨37, by omega⟩, -837809356800), (⟨42, by omega⟩, -837809356800), (⟨45, by omega⟩, -637755520000), (⟨50, by omega⟩, -69652480000), (⟨53, by omega⟩, -637755520000), (⟨61, by omega⟩, -116224896000), (⟨69, by omega⟩, -83828940800), (⟨74, by omega⟩, -837809356800), (⟨77, by omega⟩, -637755520000), (⟨82, by omega⟩, -69652480000), (⟨85, by omega⟩, -637755520000), (⟨90, by omega⟩, -1275511040000), (⟨93, by omega⟩, -1275511040000)]
  nu := [(⟨0, by omega⟩, -637755520000), (⟨3, by omega⟩, 637755520000), (⟨4, by omega⟩, 637755520000), (⟨5, by omega⟩, -837809356800), (⟨10, by omega⟩, -637755520000), (⟨11, by omega⟩, 100026918400), (⟨12, by omega⟩, 637755520000), (⟨13, by omega⟩, 637755520000), (⟨14, by omega⟩, 637755520000), (⟨15, by omega⟩, -100026918400), (⟨16, by omega⟩, -100026918400), (⟨17, by omega⟩, -100026918400), (⟨18, by omega⟩, -637755520000), (⟨19, by omega⟩, -637755520000), (⟨20, by omega⟩, -637755520000), (⟨21, by omega⟩, 637755520000), (⟨22, by omega⟩, 83828940800), (⟨23, by omega⟩, 637755520000), (⟨24, by omega⟩, 637755520000), (⟨25, by omega⟩, -83828940800), (⟨26, by omega⟩, -637755520000), (⟨27, by omega⟩, -637755520000), (⟨28, by omega⟩, -116224896000), (⟨29, by omega⟩, -83828940800), (⟨30, by omega⟩, -1545217356800), (⟨31, by omega⟩, 907461836800), (⟨32, by omega⟩, 907461836800), (⟨33, by omega⟩, 1475564876800), (⟨34, by omega⟩, 707408000000), (⟨35, by omega⟩, -837809356800), (⟨36, by omega⟩, -837809356800), (⟨37, by omega⟩, -69652480000), (⟨38, by omega⟩, -837809356800), (⟨39, by omega⟩, -69652480000), (⟨40, by omega⟩, -637755520000), (⟨41, by omega⟩, -637755520000)]
  claimed := 1692012924995719460611553890795520000
}
def branch_box_2743 : RatBox 8 := { lower := box_2743.profileLo, upper := box_2743.profileHi }
def accepted_2743 : Bool := checkAt 527 1000 box_2743 cert_2743

def box_2746 : Box := { S := 51200, lo := ![0, 36440, 0, 38640, 50560, 640, 49920, 640], hi := ![1280, 36880, 2560, 39520, 51200, 1280, 51200, 1280] }
def cert_2746 : Certificate := {
  mu := [(⟨4, by omega⟩, -1280), (⟨6, by omega⟩, -51200), (⟨13, by omega⟩, -51200), (⟨21, by omega⟩, -51200), (⟨29, by omega⟩, -51200), (⟨34, by omega⟩, -51200), (⟨45, by omega⟩, -51200), (⟨53, by omega⟩, -51200), (⟨62, by omega⟩, -51200), (⟨69, by omega⟩, -51200), (⟨77, by omega⟩, -51200), (⟨85, by omega⟩, -51200), (⟨90, by omega⟩, -102400), (⟨93, by omega⟩, -102400)]
  nu := [(⟨0, by omega⟩, -51200), (⟨3, by omega⟩, 51200), (⟨4, by omega⟩, 51200), (⟨10, by omega⟩, -51200), (⟨11, by omega⟩, 51200), (⟨12, by omega⟩, 51200), (⟨13, by omega⟩, 51200), (⟨14, by omega⟩, 51200), (⟨15, by omega⟩, -51200), (⟨16, by omega⟩, -51200), (⟨17, by omega⟩, -51200), (⟨18, by omega⟩, -51200), (⟨19, by omega⟩, -51200), (⟨20, by omega⟩, -51200), (⟨21, by omega⟩, 51200), (⟨22, by omega⟩, 51200), (⟨23, by omega⟩, 51200), (⟨24, by omega⟩, 51200), (⟨25, by omega⟩, -51200), (⟨26, by omega⟩, -51200), (⟨27, by omega⟩, -51200), (⟨28, by omega⟩, -51200), (⟨29, by omega⟩, -51200), (⟨30, by omega⟩, -51200), (⟨33, by omega⟩, 51200), (⟨34, by omega⟩, 51200), (⟨40, by omega⟩, -51200), (⟨41, by omega⟩, -51200)]
  claimed := 69911183360000
}
def branch_box_2746 : RatBox 8 := { lower := box_2746.profileLo, upper := box_2746.profileHi }
def accepted_2746 : Bool := checkAt 527 1000 box_2746 cert_2746

def box_2748 : Box := { S := 51200, lo := ![0, 36000, 0, 39080, 50560, 640, 49920, 640], hi := ![1280, 36440, 2560, 39520, 51200, 1280, 51200, 1280] }
def cert_2748 : Certificate := {
  mu := [(⟨4, by omega⟩, -1280), (⟨6, by omega⟩, -51200), (⟨45, by omega⟩, -51200), (⟨53, by omega⟩, -51200), (⟨77, by omega⟩, -51200), (⟨85, by omega⟩, -51200), (⟨90, by omega⟩, -102400), (⟨93, by omega⟩, -102400)]
  nu := [(⟨0, by omega⟩, -51200), (⟨3, by omega⟩, 51200), (⟨4, by omega⟩, 51200), (⟨10, by omega⟩, -51200), (⟨12, by omega⟩, 51200), (⟨13, by omega⟩, 51200), (⟨14, by omega⟩, 51200), (⟨18, by omega⟩, -51200), (⟨19, by omega⟩, -51200), (⟨20, by omega⟩, -51200), (⟨21, by omega⟩, 51200), (⟨23, by omega⟩, 51200), (⟨24, by omega⟩, 51200), (⟨26, by omega⟩, -51200), (⟨27, by omega⟩, -51200), (⟨30, by omega⟩, -51200), (⟨33, by omega⟩, 51200), (⟨34, by omega⟩, 51200), (⟨40, by omega⟩, -51200), (⟨41, by omega⟩, -51200)]
  claimed := 69911183360000
}
def branch_box_2748 : RatBox 8 := { lower := box_2748.profileLo, upper := box_2748.profileHi }
def accepted_2748 : Bool := checkAt 527 1000 box_2748 cert_2748

end PeaceableQueens.UpperBound.Generated.Even.Core
