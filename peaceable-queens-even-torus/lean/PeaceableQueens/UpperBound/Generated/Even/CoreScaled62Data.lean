import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_3100 : Box := { S := 3164160, lo := ![118656, 2224800, 79104, 2387952, 3085056, 0, 3085056, 0], hi := ![158208, 2279184, 158208, 2442336, 3164160, 79104, 3164160, 79104] }
def cert_3100 : Certificate := {
  mu := [(⟨5, by omega⟩, -163840), (⟨6, by omega⟩, -3000320), (⟨9, by omega⟩, -163840), (⟨13, by omega⟩, -3000320), (⟨22, by omega⟩, -3000320), (⟨34, by omega⟩, -3000320), (⟨37, by omega⟩, -163840), (⟨42, by omega⟩, -163840), (⟨50, by omega⟩, -163840), (⟨62, by omega⟩, -163840), (⟨74, by omega⟩, -163840), (⟨78, by omega⟩, -3000320), (⟨82, by omega⟩, -163840), (⟨89, by omega⟩, -3000320), (⟨90, by omega⟩, -3000320)]
  nu := [(⟨0, by omega⟩, -3000320), (⟨3, by omega⟩, 3000320), (⟨4, by omega⟩, 3000320), (⟨5, by omega⟩, -163840), (⟨10, by omega⟩, -3000320), (⟨11, by omega⟩, 3000320), (⟨12, by omega⟩, 3000320), (⟨13, by omega⟩, 3000320), (⟨15, by omega⟩, -3000320), (⟨16, by omega⟩, -3000320), (⟨18, by omega⟩, -3000320), (⟨20, by omega⟩, -3000320), (⟨21, by omega⟩, 3000320), (⟨22, by omega⟩, 3000320), (⟨25, by omega⟩, -3000320), (⟨28, by omega⟩, -163840), (⟨30, by omega⟩, -3328000), (⟨31, by omega⟩, 327680), (⟨32, by omega⟩, 327680), (⟨33, by omega⟩, 3164160), (⟨34, by omega⟩, 3164160), (⟨35, by omega⟩, -163840), (⟨36, by omega⟩, -163840), (⟨37, by omega⟩, -163840), (⟨38, by omega⟩, -163840), (⟨39, by omega⟩, -163840), (⟨40, by omega⟩, -3000320)]
  claimed := 16659425288886681600
}
def branch_box_3100 : RatBox 8 := { lower := box_3100.profileLo, upper := box_3100.profileHi }
def accepted_3100 : Bool := checkAt 527 1000 box_3100 cert_3100

def box_3102 : Box := { S := 4730419200, lo := ![118260480, 3326076000, 118260480, 3569988240, 4612158720, 59130240, 4612158720, 0], hi := ![177390720, 3407380080, 236520960, 3651292320, 4730419200, 118260480, 4730419200, 118260480] }
def cert_3102 : Certificate := {
  mu := [(⟨4, by omega⟩, -112136960), (⟨5, by omega⟩, -244940800), (⟨6, by omega⟩, -4485478400), (⟨10, by omega⟩, -244940800), (⟨14, by omega⟩, -4485478400), (⟨22, by omega⟩, -4485478400), (⟨30, by omega⟩, -240025600), (⟨33, by omega⟩, -4485478400), (⟨37, by omega⟩, -244940800), (⟨42, by omega⟩, -244940800), (⟨45, by omega⟩, -4485478400), (⟨50, by omega⟩, -244940800), (⟨54, by omega⟩, -240025600), (⟨61, by omega⟩, -4485478400), (⟨70, by omega⟩, -240025600), (⟨74, by omega⟩, -244940800), (⟨77, by omega⟩, -4485478400), (⟨82, by omega⟩, -244940800), (⟨86, by omega⟩, -240025600), (⟨90, by omega⟩, -8970956800), (⟨94, by omega⟩, -480051200)]
  nu := [(⟨0, by omega⟩, -4485478400), (⟨3, by omega⟩, 4485478400), (⟨4, by omega⟩, 4485478400), (⟨5, by omega⟩, -244940800), (⟨10, by omega⟩, -4485478400), (⟨11, by omega⟩, 4485478400), (⟨12, by omega⟩, 4485478400), (⟨13, by omega⟩, 4485478400), (⟨14, by omega⟩, 240025600), (⟨15, by omega⟩, -4485478400), (⟨16, by omega⟩, -4485478400), (⟨17, by omega⟩, -240025600), (⟨18, by omega⟩, -4485478400), (⟨19, by omega⟩, -240025600), (⟨20, by omega⟩, -4485478400), (⟨21, by omega⟩, 4485478400), (⟨22, by omega⟩, 4485478400), (⟨23, by omega⟩, 4485478400), (⟨24, by omega⟩, 240025600), (⟨25, by omega⟩, -4485478400), (⟨26, by omega⟩, -4485478400), (⟨27, by omega⟩, -240025600), (⟨28, by omega⟩, -4485478400), (⟨29, by omega⟩, -240025600), (⟨30, by omega⟩, -4975360000), (⟨31, by omega⟩, 489881600), (⟨32, by omega⟩, 489881600), (⟨33, by omega⟩, 4730419200), (⟨34, by omega⟩, 4730419200), (⟨35, by omega⟩, -244940800), (⟨36, by omega⟩, -244940800), (⟨37, by omega⟩, -244940800), (⟨38, by omega⟩, -244940800), (⟨39, by omega⟩, -244940800), (⟨40, by omega⟩, -4485478400), (⟨41, by omega⟩, -240025600)]
  claimed := 55322359640182799920005120000
}
def branch_box_3102 : RatBox 8 := { lower := box_3102.profileLo, upper := box_3102.profileHi }
def accepted_3102 : Bool := checkAt 527 1000 box_3102 cert_3102

def box_3103 : Box := { S := 1475564876800, lo := ![36889121920, 1037506554000, 36889121920, 1113590367960, 1438675754880, 0, 1438675754880, 0], hi := ![55333682880, 1062867825320, 73778243840, 1138951639280, 1457120315840, 18444560960, 1475564876800, 36889121920] }
def cert_3103 : Certificate := {
  mu := [(⟨5, by omega⟩, -837809356800), (⟨6, by omega⟩, -637755520000), (⟨10, by omega⟩, -837809356800), (⟨14, by omega⟩, -637755520000), (⟨21, by omega⟩, -837809356800), (⟨33, by omega⟩, -637755520000), (⟨37, by omega⟩, -837809356800), (⟨42, by omega⟩, -837809356800), (⟨45, by omega⟩, -187219968000), (⟨50, by omega⟩, -69652480000), (⟨62, by omega⟩, -837809356800), (⟨74, by omega⟩, -837809356800), (⟨82, by omega⟩, -69652480000), (⟨90, by omega⟩, -1275511040000)]
  nu := [(⟨0, by omega⟩, -637755520000), (⟨3, by omega⟩, 637755520000), (⟨4, by omega⟩, 637755520000), (⟨5, by omega⟩, -837809356800), (⟨10, by omega⟩, -637755520000), (⟨11, by omega⟩, 637755520000), (⟨12, by omega⟩, 637755520000), (⟨15, by omega⟩, -637755520000), (⟨16, by omega⟩, -837809356800), (⟨20, by omega⟩, -637755520000), (⟨21, by omega⟩, 637755520000), (⟨22, by omega⟩, 637755520000), (⟨23, by omega⟩, 187219968000), (⟨25, by omega⟩, -637755520000), (⟨26, by omega⟩, -187219968000), (⟨28, by omega⟩, -837809356800), (⟨30, by omega⟩, -1545217356800), (⟨31, by omega⟩, 907461836800), (⟨32, by omega⟩, 907461836800), (⟨33, by omega⟩, 1475564876800), (⟨34, by omega⟩, 707408000000), (⟨35, by omega⟩, -837809356800), (⟨36, by omega⟩, -837809356800), (⟨37, by omega⟩, -69652480000), (⟨38, by omega⟩, -837809356800), (⟨39, by omega⟩, -69652480000), (⟨40, by omega⟩, -637755520000)]
  claimed := 1692719090909163316950789022679040000
}
def branch_box_3103 : RatBox 8 := { lower := box_3103.profileLo, upper := box_3103.profileHi }
def accepted_3103 : Bool := checkAt 527 1000 box_3103 cert_3103

def box_3106 : Box := { S := 17254400, lo := ![431360, 12280280, 431360, 13021680, 17038720, 0, 16823040, 0], hi := ![647040, 12428560, 862720, 13318240, 17254400, 215680, 17254400, 431360] }
def cert_3106 : Certificate := {
  mu := [(⟨4, by omega⟩, -431360), (⟨6, by omega⟩, -17254400), (⟨14, by omega⟩, -17254400), (⟨33, by omega⟩, -17254400), (⟨54, by omega⟩, -1638400), (⟨70, by omega⟩, -1638400), (⟨90, by omega⟩, -34508800)]
  nu := [(⟨0, by omega⟩, -17254400), (⟨3, by omega⟩, 17254400), (⟨4, by omega⟩, 17254400), (⟨10, by omega⟩, -17254400), (⟨11, by omega⟩, 17254400), (⟨12, by omega⟩, 17254400), (⟨15, by omega⟩, -17254400), (⟨20, by omega⟩, -17254400), (⟨21, by omega⟩, 17254400), (⟨22, by omega⟩, 17254400), (⟨24, by omega⟩, 1638400), (⟨25, by omega⟩, -17254400), (⟨27, by omega⟩, -1638400), (⟨29, by omega⟩, -1638400), (⟨30, by omega⟩, -17254400), (⟨33, by omega⟩, 17254400), (⟨34, by omega⟩, 17254400), (⟨40, by omega⟩, -17254400)]
  claimed := 2674088177065000960000
}
def branch_box_3106 : RatBox 8 := { lower := box_3106.profileLo, upper := box_3106.profileHi }
def accepted_3106 : Bool := checkAt 527 1000 box_3106 cert_3106

def box_3108 : Box := { S := 4044800, lo := ![101120, 2844000, 101120, 3087320, 3994240, 0, 3943680, 0], hi := ![151680, 2878760, 202240, 3122080, 4044800, 50560, 4044800, 101120] }
def cert_3108 : Certificate := {
  mu := [(⟨4, by omega⟩, -101120), (⟨6, by omega⟩, -4044800), (⟨14, by omega⟩, -4044800), (⟨33, by omega⟩, -4044800), (⟨54, by omega⟩, -409600), (⟨69, by omega⟩, -409600), (⟨90, by omega⟩, -8089600)]
  nu := [(⟨0, by omega⟩, -4044800), (⟨3, by omega⟩, 4044800), (⟨4, by omega⟩, 4044800), (⟨10, by omega⟩, -4044800), (⟨11, by omega⟩, 4044800), (⟨12, by omega⟩, 4044800), (⟨15, by omega⟩, -4044800), (⟨20, by omega⟩, -4044800), (⟨21, by omega⟩, 4044800), (⟨22, by omega⟩, 4044800), (⟨24, by omega⟩, 409600), (⟨25, by omega⟩, -4044800), (⟨27, by omega⟩, -409600), (⟨29, by omega⟩, -409600), (⟨30, by omega⟩, -4044800), (⟨33, by omega⟩, 4044800), (⟨34, by omega⟩, 4044800), (⟨40, by omega⟩, -4044800)]
  claimed := 34448260378132480000
}
def branch_box_3108 : RatBox 8 := { lower := box_3108.profileLo, upper := box_3108.profileHi }
def accepted_3108 : Bool := checkAt 527 1000 box_3108 cert_3108

def box_3110 : Box := { S := 3200, lo := ![80, 2305, 80, 2415, 3120, 0, 3120, 0], hi := ![160, 2360, 160, 2470, 3200, 80, 3200, 80] }
def cert_3110 : Certificate := {
  mu := [(⟨6, by omega⟩, -3200), (⟨13, by omega⟩, -3200), (⟨34, by omega⟩, -3200), (⟨46, by omega⟩, -3200), (⟨62, by omega⟩, -3200), (⟨89, by omega⟩, -6400)]
  nu := [(⟨0, by omega⟩, -3200), (⟨3, by omega⟩, 3200), (⟨4, by omega⟩, 3200), (⟨10, by omega⟩, -3200), (⟨11, by omega⟩, 3200), (⟨12, by omega⟩, 3200), (⟨15, by omega⟩, -3200), (⟨20, by omega⟩, -3200), (⟨21, by omega⟩, 3200), (⟨22, by omega⟩, 3200), (⟨23, by omega⟩, 3200), (⟨25, by omega⟩, -3200), (⟨26, by omega⟩, -3200), (⟨28, by omega⟩, -3200), (⟨30, by omega⟩, -3200), (⟨33, by omega⟩, 3200), (⟨34, by omega⟩, 3200), (⟨40, by omega⟩, -3200)]
  claimed := 16814080000
}
def branch_box_3110 : RatBox 8 := { lower := box_3110.profileLo, upper := box_3110.profileHi }
def accepted_3110 : Bool := checkAt 527 1000 box_3110 cert_3110

def box_3112 : Box := { S := 7910400, lo := ![296640, 5697960, 197760, 5833920, 7712640, 0, 7712640, 0], hi := ![395520, 5833920, 395520, 5969880, 7910400, 197760, 7910400, 197760] }
def cert_3112 : Certificate := {
  mu := [(⟨5, by omega⟩, -409600), (⟨6, by omega⟩, -7500800), (⟨9, by omega⟩, -409600), (⟨13, by omega⟩, -7500800), (⟨22, by omega⟩, -7500800), (⟨34, by omega⟩, -7500800), (⟨37, by omega⟩, -409600), (⟨42, by omega⟩, -409600), (⟨50, by omega⟩, -409600), (⟨62, by omega⟩, -409600), (⟨74, by omega⟩, -409600), (⟨78, by omega⟩, -7500800), (⟨82, by omega⟩, -409600), (⟨89, by omega⟩, -7500800), (⟨90, by omega⟩, -7500800)]
  nu := [(⟨0, by omega⟩, -7500800), (⟨3, by omega⟩, 7500800), (⟨4, by omega⟩, 7500800), (⟨5, by omega⟩, -409600), (⟨10, by omega⟩, -7500800), (⟨11, by omega⟩, 7500800), (⟨12, by omega⟩, 7500800), (⟨13, by omega⟩, 7500800), (⟨15, by omega⟩, -7500800), (⟨16, by omega⟩, -7500800), (⟨18, by omega⟩, -7500800), (⟨20, by omega⟩, -7500800), (⟨21, by omega⟩, 7500800), (⟨22, by omega⟩, 7500800), (⟨25, by omega⟩, -7500800), (⟨28, by omega⟩, -409600), (⟨30, by omega⟩, -8320000), (⟨31, by omega⟩, 819200), (⟨32, by omega⟩, 819200), (⟨33, by omega⟩, 7910400), (⟨34, by omega⟩, 7910400), (⟨35, by omega⟩, -409600), (⟨36, by omega⟩, -409600), (⟨37, by omega⟩, -409600), (⟨38, by omega⟩, -409600), (⟨39, by omega⟩, -409600), (⟨40, by omega⟩, -7500800)]
  claimed := 260217824459489280000
}
def branch_box_3112 : RatBox 8 := { lower := box_3112.profileLo, upper := box_3112.profileHi }
def accepted_3112 : Bool := checkAt 527 1000 box_3112 cert_3112

def box_3114 : Box := { S := 4603852800, lo := ![115096320, 3316212720, 115096320, 3395341440, 4488756480, 57548160, 4488756480, 0], hi := ![172644480, 3395341440, 230192640, 3474470160, 4603852800, 115096320, 4603852800, 115096320] }
def cert_3114 : Certificate := {
  mu := [(⟨4, by omega⟩, -109136640), (⟨5, by omega⟩, -238387200), (⟨6, by omega⟩, -4365465600), (⟨9, by omega⟩, -238387200), (⟨13, by omega⟩, -4365465600), (⟨21, by omega⟩, -4365465600), (⟨29, by omega⟩, -240025600), (⟨33, by omega⟩, -4365465600), (⟨37, by omega⟩, -238387200), (⟨42, by omega⟩, -238387200), (⟨45, by omega⟩, -4365465600), (⟨50, by omega⟩, -238387200), (⟨54, by omega⟩, -240025600), (⟨61, by omega⟩, -4365465600), (⟨70, by omega⟩, -240025600), (⟨74, by omega⟩, -238387200), (⟨77, by omega⟩, -4365465600), (⟨82, by omega⟩, -238387200), (⟨86, by omega⟩, -240025600), (⟨90, by omega⟩, -8730931200), (⟨94, by omega⟩, -480051200)]
  nu := [(⟨0, by omega⟩, -4365465600), (⟨3, by omega⟩, 4365465600), (⟨4, by omega⟩, 4365465600), (⟨5, by omega⟩, -238387200), (⟨10, by omega⟩, -4365465600), (⟨11, by omega⟩, 4365465600), (⟨12, by omega⟩, 4365465600), (⟨13, by omega⟩, 4365465600), (⟨14, by omega⟩, 240025600), (⟨15, by omega⟩, -4365465600), (⟨16, by omega⟩, -4365465600), (⟨17, by omega⟩, -240025600), (⟨18, by omega⟩, -4365465600), (⟨19, by omega⟩, -240025600), (⟨20, by omega⟩, -4365465600), (⟨21, by omega⟩, 4365465600), (⟨22, by omega⟩, 4365465600), (⟨23, by omega⟩, 4365465600), (⟨24, by omega⟩, 240025600), (⟨25, by omega⟩, -4365465600), (⟨26, by omega⟩, -4365465600), (⟨27, by omega⟩, -240025600), (⟨28, by omega⟩, -4365465600), (⟨29, by omega⟩, -240025600), (⟨30, by omega⟩, -4842240000), (⟨31, by omega⟩, 476774400), (⟨32, by omega⟩, 476774400), (⟨33, by omega⟩, 4603852800), (⟨34, by omega⟩, 4603852800), (⟨35, by omega⟩, -238387200), (⟨36, by omega⟩, -238387200), (⟨37, by omega⟩, -238387200), (⟨38, by omega⟩, -238387200), (⟨39, by omega⟩, -238387200), (⟨40, by omega⟩, -4365465600), (⟨41, by omega⟩, -240025600)]
  claimed := 51002506308726582938173440000
}
def branch_box_3114 : RatBox 8 := { lower := box_3114.profileLo, upper := box_3114.profileHi }
def accepted_3114 : Bool := checkAt 527 1000 box_3114 cert_3114

def box_3117 : Box := { S := 604800, lo := ![15120, 435645, 15120, 446040, 589680, 0, 589680, 0], hi := ![22680, 446040, 30240, 456435, 597240, 7560, 597240, 15120] }
def cert_3117 : Certificate := {
  mu := [(⟨5, by omega⟩, -349440), (⟨6, by omega⟩, -255360), (⟨9, by omega⟩, -349440), (⟨14, by omega⟩, -255360), (⟨22, by omega⟩, -349440), (⟨33, by omega⟩, -255360), (⟨37, by omega⟩, -349440), (⟨42, by omega⟩, -349440), (⟨45, by omega⟩, -66560), (⟨50, by omega⟩, -349440), (⟨62, by omega⟩, -349440), (⟨74, by omega⟩, -349440), (⟨82, by omega⟩, -349440), (⟨89, by omega⟩, -698880)]
  nu := [(⟨0, by omega⟩, -349440), (⟨3, by omega⟩, 349440), (⟨4, by omega⟩, 349440), (⟨5, by omega⟩, -349440), (⟨10, by omega⟩, -255360), (⟨11, by omega⟩, 255360), (⟨12, by omega⟩, 255360), (⟨15, by omega⟩, -255360), (⟨16, by omega⟩, -349440), (⟨20, by omega⟩, -255360), (⟨21, by omega⟩, 255360), (⟨22, by omega⟩, 255360), (⟨23, by omega⟩, 66560), (⟨25, by omega⟩, -255360), (⟨26, by omega⟩, -66560), (⟨28, by omega⟩, -349440), (⟨30, by omega⟩, -1048320), (⟨31, by omega⟩, 698880), (⟨32, by omega⟩, 698880), (⟨33, by omega⟩, 698880), (⟨34, by omega⟩, 698880), (⟨35, by omega⟩, -349440), (⟨36, by omega⟩, -349440), (⟨37, by omega⟩, -349440), (⟨38, by omega⟩, -349440), (⟨39, by omega⟩, -349440), (⟨40, by omega⟩, -349440)]
  claimed := 115936031877120000
}
def branch_box_3117 : RatBox 8 := { lower := box_3117.profileLo, upper := box_3117.profileHi }
def accepted_3117 : Bool := checkAt 527 1000 box_3117 cert_3117

def box_3120 : Box := { S := 11175065600, lo := ![279376640, 8145575160, 279376640, 8241610880, 10895688960, 0, 11035377280, 0], hi := ![419064960, 8241610880, 558753280, 8433682320, 11035377280, 139688320, 11175065600, 279376640] }
def cert_3120 : Certificate := {
  mu := [(⟨5, by omega⟩, -568524800), (⟨6, by omega⟩, -10606540800), (⟨10, by omega⟩, -568524800), (⟨13, by omega⟩, -10606540800), (⟨22, by omega⟩, -568524800), (⟨33, by omega⟩, -10606540800), (⟨37, by omega⟩, -568524800), (⟨42, by omega⟩, -568524800), (⟨46, by omega⟩, -104857600), (⟨50, by omega⟩, -568524800), (⟨62, by omega⟩, -568524800), (⟨74, by omega⟩, -568524800), (⟨82, by omega⟩, -568524800), (⟨89, by omega⟩, -21213081600)]
  nu := [(⟨0, by omega⟩, -10606540800), (⟨3, by omega⟩, 10606540800), (⟨4, by omega⟩, 10606540800), (⟨5, by omega⟩, -568524800), (⟨10, by omega⟩, -10606540800), (⟨11, by omega⟩, 10606540800), (⟨12, by omega⟩, 10606540800), (⟨15, by omega⟩, -10606540800), (⟨16, by omega⟩, -568524800), (⟨20, by omega⟩, -10606540800), (⟨21, by omega⟩, 10606540800), (⟨22, by omega⟩, 10606540800), (⟨23, by omega⟩, 104857600), (⟨25, by omega⟩, -10606540800), (⟨26, by omega⟩, -104857600), (⟨28, by omega⟩, -568524800), (⟨30, by omega⟩, -11743590400), (⟨31, by omega⟩, 1137049600), (⟨32, by omega⟩, 1137049600), (⟨33, by omega⟩, 11175065600), (⟨34, by omega⟩, 11175065600), (⟨35, by omega⟩, -568524800), (⟨36, by omega⟩, -568524800), (⟨37, by omega⟩, -568524800), (⟨38, by omega⟩, -568524800), (⟨39, by omega⟩, -568524800), (⟨40, by omega⟩, -10606540800)]
  claimed := 726908182810868771347496960000
}
def branch_box_3120 : RatBox 8 := { lower := box_3120.profileLo, upper := box_3120.profileHi }
def accepted_3120 : Bool := checkAt 527 1000 box_3120 cert_3120

def box_3122 : Box := { S := 5764659200, lo := ![144116480, 4152356080, 144116480, 4300976200, 5620542720, 0, 5692600960, 0], hi := ![216174720, 4201896120, 288232960, 4350516240, 5692600960, 72058240, 5764659200, 144116480] }
def cert_3122 : Certificate := {
  mu := [(⟨5, by omega⟩, -293273600), (⟨6, by omega⟩, -5471385600), (⟨10, by omega⟩, -293273600), (⟨13, by omega⟩, -5471385600), (⟨22, by omega⟩, -267059200), (⟨33, by omega⟩, -5471385600), (⟨37, by omega⟩, -293273600), (⟨42, by omega⟩, -293273600), (⟨46, by omega⟩, -26214400), (⟨50, by omega⟩, -293273600), (⟨54, by omega⟩, -5471385600), (⟨62, by omega⟩, -26214400), (⟨70, by omega⟩, -5471385600), (⟨74, by omega⟩, -293273600), (⟨82, by omega⟩, -293273600), (⟨89, by omega⟩, -10942771200), (⟨93, by omega⟩, -52428800)]
  nu := [(⟨0, by omega⟩, -5471385600), (⟨3, by omega⟩, 5471385600), (⟨4, by omega⟩, 5471385600), (⟨5, by omega⟩, -293273600), (⟨10, by omega⟩, -5471385600), (⟨11, by omega⟩, 5471385600), (⟨12, by omega⟩, 5471385600), (⟨15, by omega⟩, -5471385600), (⟨16, by omega⟩, -267059200), (⟨20, by omega⟩, -5471385600), (⟨21, by omega⟩, 5471385600), (⟨22, by omega⟩, 5471385600), (⟨23, by omega⟩, 26214400), (⟨24, by omega⟩, 5471385600), (⟨25, by omega⟩, -5471385600), (⟨26, by omega⟩, -26214400), (⟨27, by omega⟩, -5471385600), (⟨28, by omega⟩, -26214400), (⟨29, by omega⟩, -5471385600), (⟨30, by omega⟩, -6057932800), (⟨31, by omega⟩, 586547200), (⟨32, by omega⟩, 586547200), (⟨33, by omega⟩, 5764659200), (⟨34, by omega⟩, 5764659200), (⟨35, by omega⟩, -293273600), (⟨36, by omega⟩, -293273600), (⟨37, by omega⟩, -293273600), (⟨38, by omega⟩, -293273600), (⟨39, by omega⟩, -293273600), (⟨40, by omega⟩, -5471385600), (⟨41, by omega⟩, -26214400)]
  claimed := 99780105972188850497781760000
}
def branch_box_3122 : RatBox 8 := { lower := box_3122.profileLo, upper := box_3122.profileHi }
def accepted_3122 : Bool := checkAt 527 1000 box_3122 cert_3122

def box_3124 : Box := { S := 51200, lo := ![1280, 37320, 1280, 37760, 50560, 0, 49920, 0], hi := ![1920, 37760, 2560, 38640, 51200, 640, 51200, 1280] }
def cert_3124 : Certificate := {
  mu := [(⟨4, by omega⟩, -1280), (⟨6, by omega⟩, -51200), (⟨13, by omega⟩, -51200), (⟨22, by omega⟩, -51200), (⟨33, by omega⟩, -51200), (⟨54, by omega⟩, -51200), (⟨70, by omega⟩, -51200), (⟨78, by omega⟩, -51200), (⟨90, by omega⟩, -102400)]
  nu := [(⟨0, by omega⟩, -51200), (⟨3, by omega⟩, 51200), (⟨4, by omega⟩, 51200), (⟨10, by omega⟩, -51200), (⟨11, by omega⟩, 51200), (⟨12, by omega⟩, 51200), (⟨13, by omega⟩, 51200), (⟨15, by omega⟩, -51200), (⟨16, by omega⟩, -51200), (⟨18, by omega⟩, -51200), (⟨20, by omega⟩, -51200), (⟨21, by omega⟩, 51200), (⟨22, by omega⟩, 51200), (⟨24, by omega⟩, 51200), (⟨25, by omega⟩, -51200), (⟨27, by omega⟩, -51200), (⟨29, by omega⟩, -51200), (⟨30, by omega⟩, -51200), (⟨33, by omega⟩, 51200), (⟨34, by omega⟩, 51200), (⟨40, by omega⟩, -51200)]
  claimed := 69869240320000
}
def branch_box_3124 : RatBox 8 := { lower := box_3124.profileLo, upper := box_3124.profileHi }
def accepted_3124 : Bool := checkAt 527 1000 box_3124 cert_3124

def box_3126 : Box := { S := 8345600, lo := ![208640, 6011440, 208640, 6226600, 8241280, 0, 8136960, 0], hi := ![312960, 6083160, 417280, 6298320, 8345600, 104320, 8345600, 208640] }
def cert_3126 : Certificate := {
  mu := [(⟨4, by omega⟩, -208640), (⟨6, by omega⟩, -8345600), (⟨13, by omega⟩, -8345600), (⟨33, by omega⟩, -8345600), (⟨54, by omega⟩, -819200), (⟨70, by omega⟩, -819200), (⟨90, by omega⟩, -16691200)]
  nu := [(⟨0, by omega⟩, -8345600), (⟨3, by omega⟩, 8345600), (⟨4, by omega⟩, 8345600), (⟨10, by omega⟩, -8345600), (⟨11, by omega⟩, 8345600), (⟨12, by omega⟩, 8345600), (⟨15, by omega⟩, -8345600), (⟨20, by omega⟩, -8345600), (⟨21, by omega⟩, 8345600), (⟨22, by omega⟩, 8345600), (⟨24, by omega⟩, 819200), (⟨25, by omega⟩, -8345600), (⟨27, by omega⟩, -819200), (⟨29, by omega⟩, -819200), (⟨30, by omega⟩, -8345600), (⟨33, by omega⟩, 8345600), (⟨34, by omega⟩, 8345600), (⟨40, by omega⟩, -8345600)]
  claimed := 302586002908119040000
}
def branch_box_3126 : RatBox 8 := { lower := box_3126.profileLo, upper := box_3126.profileHi }
def accepted_3126 : Bool := checkAt 527 1000 box_3126 cert_3126

def box_3128 : Box := { S := 199185600, lo := ![0, 133205370, 9959280, 146899380, 189226320, 9959280, 189226320, 0], hi := ![9959280, 146899380, 19918560, 160593390, 199185600, 19918560, 199185600, 19918560] }
def cert_3128 : Certificate := {
  mu := [(⟨4, by omega⟩, -42166800), (⟨5, by omega⟩, -103795200), (⟨6, by omega⟩, -95390400), (⟨9, by omega⟩, -103795200), (⟨13, by omega⟩, -46131200), (⟨21, by omega⟩, -46131200), (⟨30, by omega⟩, -46131200), (⟨33, by omega⟩, -95390400), (⟨37, by omega⟩, -103795200), (⟨42, by omega⟩, -103795200), (⟨45, by omega⟩, -95390400), (⟨53, by omega⟩, -2366400), (⟨54, by omega⟩, -93024000), (⟨61, by omega⟩, -95390400), (⟨66, by omega⟩, -38385600), (⟨70, by omega⟩, -95390400), (⟨74, by omega⟩, -103795200), (⟨77, by omega⟩, -95390400), (⟨86, by omega⟩, -95390400), (⟨90, by omega⟩, -114009600), (⟨94, by omega⟩, -190780800)]
  nu := [(⟨0, by omega⟩, -95390400), (⟨2, by omega⟩, 38385600), (⟨3, by omega⟩, 57004800), (⟨4, by omega⟩, 95390400), (⟨5, by omega⟩, -103795200), (⟨9, by omega⟩, -38385600), (⟨10, by omega⟩, -95390400), (⟨11, by omega⟩, 46131200), (⟨12, by omega⟩, 95390400), (⟨13, by omega⟩, 95390400), (⟨14, by omega⟩, 95390400), (⟨15, by omega⟩, -46131200), (⟨16, by omega⟩, -46131200), (⟨17, by omega⟩, -46131200), (⟨18, by omega⟩, -95390400), (⟨19, by omega⟩, -95390400), (⟨20, by omega⟩, -95390400), (⟨21, by omega⟩, 95390400), (⟨22, by omega⟩, 95390400), (⟨23, by omega⟩, 95390400), (⟨24, by omega⟩, 95390400), (⟨25, by omega⟩, -95390400), (⟨26, by omega⟩, -95390400), (⟨27, by omega⟩, -95390400), (⟨28, by omega⟩, -95390400), (⟨29, by omega⟩, -95390400), (⟨30, by omega⟩, -160800000), (⟨31, by omega⟩, 103795200), (⟨32, by omega⟩, 103795200), (⟨33, by omega⟩, 160800000), (⟨34, by omega⟩, 57004800), (⟨35, by omega⟩, -103795200), (⟨36, by omega⟩, -103795200), (⟨38, by omega⟩, -103795200), (⟨40, by omega⟩, -57004800), (⟨41, by omega⟩, -95390400)]
  claimed := 4028926793389827217920000
}
def branch_box_3128 : RatBox 8 := { lower := box_3128.profileLo, upper := box_3128.profileHi }
def accepted_3128 : Bool := checkAt 527 1000 box_3128 cert_3128

def box_3130 : Box := { S := 46321600, lo := ![0, 30977570, 2316080, 34162180, 44005520, 0, 44005520, 2316080], hi := ![2316080, 34162180, 4632160, 37346790, 46321600, 2316080, 46321600, 4632160] }
def cert_3130 : Certificate := {
  mu := [(⟨5, by omega⟩, -25459200), (⟨6, by omega⟩, -20862400), (⟨9, by omega⟩, -25459200), (⟨13, by omega⟩, -5990400), (⟨21, by omega⟩, -13478400), (⟨29, by omega⟩, -5990400), (⟨33, by omega⟩, -20862400), (⟨37, by omega⟩, -25459200), (⟨42, by omega⟩, -5135360), (⟨45, by omega⟩, -5990400), (⟨53, by omega⟩, -20862400), (⟨62, by omega⟩, -5990400), (⟨69, by omega⟩, -20862400), (⟨74, by omega⟩, -5135360), (⟨85, by omega⟩, -5990400), (⟨86, by omega⟩, -14872000), (⟨89, by omega⟩, -41724800), (⟨93, by omega⟩, -11980800)]
  nu := [(⟨0, by omega⟩, -20862400), (⟨3, by omega⟩, 20862400), (⟨4, by omega⟩, 20862400), (⟨5, by omega⟩, -25459200), (⟨10, by omega⟩, -20862400), (⟨11, by omega⟩, 5990400), (⟨12, by omega⟩, 20862400), (⟨14, by omega⟩, 20862400), (⟨15, by omega⟩, -5990400), (⟨16, by omega⟩, -13478400), (⟨17, by omega⟩, -5990400), (⟨19, by omega⟩, -20862400), (⟨20, by omega⟩, -20862400), (⟨21, by omega⟩, 20862400), (⟨22, by omega⟩, 20862400), (⟨23, by omega⟩, 5990400), (⟨24, by omega⟩, 20862400), (⟨25, by omega⟩, -20862400), (⟨26, by omega⟩, -5990400), (⟨27, by omega⟩, -20862400), (⟨28, by omega⟩, -5990400), (⟨29, by omega⟩, -20862400), (⟨30, by omega⟩, -25997760), (⟨31, by omega⟩, 5135360), (⟨32, by omega⟩, 5135360), (⟨33, by omega⟩, 25997760), (⟨34, by omega⟩, 20862400), (⟨35, by omega⟩, -25459200), (⟨36, by omega⟩, -5135360), (⟨38, by omega⟩, -5135360), (⟨40, by omega⟩, -20862400), (⟨41, by omega⟩, -5990400)]
  claimed := 51562827526916293120000
}
def branch_box_3130 : RatBox 8 := { lower := box_3130.profileLo, upper := box_3130.profileHi }
def accepted_3130 : Bool := checkAt 527 1000 box_3130 cert_3130

def box_3138 : Box := { S := 957386240, lo := ![0, 640252048, 71803968, 706072352, 909516928, 0, 909516928, 0], hi := ![23934656, 673162200, 95738624, 738982504, 957386240, 47869312, 957386240, 47869312] }
def cert_3138 : Certificate := {
  mu := [(⟨5, by omega⟩, -562135040), (⟨6, by omega⟩, -395251200), (⟨10, by omega⟩, -562135040), (⟨14, by omega⟩, -246415360), (⟨21, by omega⟩, -246415360), (⟨29, by omega⟩, -246415360), (⟨33, by omega⟩, -395251200), (⟨37, by omega⟩, -562135040), (⟨41, by omega⟩, -89702400), (⟨45, by omega⟩, -166883840), (⟨62, by omega⟩, -166883840), (⟨74, by omega⟩, -89702400), (⟨77, by omega⟩, -395251200), (⟨85, by omega⟩, -395251200), (⟨89, by omega⟩, -790502400), (⟨93, by omega⟩, -1680125920)]
  nu := [(⟨0, by omega⟩, -395251200), (⟨3, by omega⟩, 395251200), (⟨4, by omega⟩, 395251200), (⟨5, by omega⟩, -562135040), (⟨10, by omega⟩, -395251200), (⟨11, by omega⟩, 246415360), (⟨12, by omega⟩, 395251200), (⟨13, by omega⟩, 395251200), (⟨14, by omega⟩, 395251200), (⟨15, by omega⟩, -246415360), (⟨16, by omega⟩, -246415360), (⟨17, by omega⟩, -246415360), (⟨18, by omega⟩, -395251200), (⟨19, by omega⟩, -395251200), (⟨20, by omega⟩, -395251200), (⟨21, by omega⟩, 395251200), (⟨22, by omega⟩, 395251200), (⟨23, by omega⟩, 166883840), (⟨25, by omega⟩, -395251200), (⟨26, by omega⟩, -166883840), (⟨28, by omega⟩, -166883840), (⟨30, by omega⟩, -484953600), (⟨31, by omega⟩, 89702400), (⟨32, by omega⟩, 89702400), (⟨33, by omega⟩, 484953600), (⟨34, by omega⟩, 395251200), (⟨35, by omega⟩, -562135040), (⟨36, by omega⟩, -89702400), (⟨38, by omega⟩, -89702400), (⟨40, by omega⟩, -395251200), (⟨41, by omega⟩, -395251200)]
  claimed := 461768887534945568587776000
}
def branch_box_3138 : RatBox 8 := { lower := box_3138.profileLo, upper := box_3138.profileHi }
def accepted_3138 : Bool := checkAt 527 1000 box_3138 cert_3138

def box_3140 : Box := { S := 106200640, lo := ![0, 71021678, 5310032, 78322972, 100890608, 2655016, 100890608, 0], hi := ![2655016, 74672325, 7965048, 81973619, 106200640, 5310032, 106200640, 5310032] }
def cert_3140 : Certificate := {
  mu := [(⟨4, by omega⟩, -21068775), (⟨5, by omega⟩, -60336640), (⟨6, by omega⟩, -45864000), (⟨9, by omega⟩, -60336640), (⟨14, by omega⟩, -19701760), (⟨21, by omega⟩, -19701760), (⟨30, by omega⟩, -19701760), (⟨33, by omega⟩, -45864000), (⟨37, by omega⟩, -60336640), (⟨41, by omega⟩, -41481440), (⟨42, by omega⟩, -12973632), (⟨45, by omega⟩, -45864000), (⟨53, by omega⟩, -45864000), (⟨62, by omega⟩, -45864000), (⟨70, by omega⟩, -45864000), (⟨74, by omega⟩, -54455072), (⟨77, by omega⟩, -45864000), (⟨86, by omega⟩, -45864000), (⟨89, by omega⟩, -49590450), (⟨94, by omega⟩, -91728000)]
  nu := [(⟨0, by omega⟩, -45864000), (⟨3, by omega⟩, 24795225), (⟨4, by omega⟩, 45864000), (⟨5, by omega⟩, -60336640), (⟨10, by omega⟩, -45864000), (⟨11, by omega⟩, 19701760), (⟨12, by omega⟩, 45864000), (⟨13, by omega⟩, 45864000), (⟨14, by omega⟩, 45864000), (⟨15, by omega⟩, -19701760), (⟨16, by omega⟩, -19701760), (⟨17, by omega⟩, -19701760), (⟨18, by omega⟩, -45864000), (⟨19, by omega⟩, -45864000), (⟨20, by omega⟩, -45864000), (⟨21, by omega⟩, 45864000), (⟨22, by omega⟩, 45864000), (⟨23, by omega⟩, 45864000), (⟨24, by omega⟩, 45864000), (⟨25, by omega⟩, -45864000), (⟨26, by omega⟩, -45864000), (⟨27, by omega⟩, -45864000), (⟨28, by omega⟩, -45864000), (⟨29, by omega⟩, -45864000), (⟨30, by omega⟩, -79250297), (⟨31, by omega⟩, 54455072), (⟨32, by omega⟩, 54455072), (⟨33, by omega⟩, 79250297), (⟨34, by omega⟩, 24795225), (⟨35, by omega⟩, -60336640), (⟨36, by omega⟩, -54455072), (⟨38, by omega⟩, -54455072), (⟨40, by omega⟩, -24795225), (⟨41, by omega⟩, -45864000)]
  claimed := 622029929613856598016000
}
def branch_box_3140 : RatBox 8 := { lower := box_3140.profileLo, upper := box_3140.profileHi }
def accepted_3140 : Bool := checkAt 527 1000 box_3140 cert_3140

def box_3142 : Box := { S := 21537280, lo := ![0, 14403056, 1076864, 15883744, 20460416, 0, 20460416, 538432], hi := ![538432, 15143400, 1615296, 16624088, 21537280, 538432, 21537280, 1076864] }
def cert_3142 : Certificate := {
  mu := [(⟨5, by omega⟩, -12513280), (⟨6, by omega⟩, -9024000), (⟨9, by omega⟩, -12513280), (⟨14, by omega⟩, -3080192), (⟨21, by omega⟩, -7688448), (⟨29, by omega⟩, -3080192), (⟨33, by omega⟩, -9024000), (⟨37, by omega⟩, -12513280), (⟨45, by omega⟩, -1744640), (⟨49, by omega⟩, -2048000), (⟨53, by omega⟩, -9024000), (⟨61, by omega⟩, -1744640), (⟨69, by omega⟩, -9024000), (⟨82, by omega⟩, -2048000), (⟨85, by omega⟩, -9024000), (⟨90, by omega⟩, -18048000), (⟨93, by omega⟩, -3489280)]
  nu := [(⟨0, by omega⟩, -9024000), (⟨3, by omega⟩, 9024000), (⟨4, by omega⟩, 9024000), (⟨5, by omega⟩, -12513280), (⟨10, by omega⟩, -9024000), (⟨11, by omega⟩, 3080192), (⟨12, by omega⟩, 9024000), (⟨14, by omega⟩, 9024000), (⟨15, by omega⟩, -3080192), (⟨16, by omega⟩, -7688448), (⟨17, by omega⟩, -3080192), (⟨19, by omega⟩, -9024000), (⟨20, by omega⟩, -9024000), (⟨21, by omega⟩, 9024000), (⟨22, by omega⟩, 9024000), (⟨23, by omega⟩, 1744640), (⟨24, by omega⟩, 9024000), (⟨25, by omega⟩, -9024000), (⟨26, by omega⟩, -1744640), (⟨27, by omega⟩, -9024000), (⟨28, by omega⟩, -1744640), (⟨29, by omega⟩, -9024000), (⟨30, by omega⟩, -11072000), (⟨31, by omega⟩, 2048000), (⟨32, by omega⟩, 2048000), (⟨33, by omega⟩, 9024000), (⟨34, by omega⟩, 11072000), (⟨35, by omega⟩, -12513280), (⟨37, by omega⟩, -2048000), (⟨39, by omega⟩, -2048000), (⟨40, by omega⟩, -9024000), (⟨41, by omega⟩, -1744640)]
  claimed := 5235875159229038592000
}
def branch_box_3142 : RatBox 8 := { lower := box_3142.profileLo, upper := box_3142.profileHi }
def accepted_3142 : Bool := checkAt 527 1000 box_3142 cert_3142

def box_3143 : Box := { S := 7074996480, lo := ![0, 4731403896, 353749824, 5217809904, 6721246656, 0, 6721246656, 0], hi := ![176874912, 4974606900, 530624736, 5461012908, 6898121568, 176874912, 7074996480, 176874912] }
def cert_3143 : Certificate := {
  mu := [(⟨5, by omega⟩, -4216012800), (⟨6, by omega⟩, -2858983680), (⟨9, by omega⟩, -4216012800), (⟨14, by omega⟩, -924057600), (⟨21, by omega⟩, -3537498240), (⟨33, by omega⟩, -2858983680), (⟨37, by omega⟩, -4216012800), (⟨41, by omega⟩, -4216012800), (⟨45, by omega⟩, -678514560), (⟨49, by omega⟩, -324423680), (⟨53, by omega⟩, -2858983680), (⟨61, by omega⟩, -678514560), (⟨69, by omega⟩, -2858983680), (⟨74, by omega⟩, -4216012800), (⟨82, by omega⟩, -324423680), (⟨89, by omega⟩, -5717967360), (⟨93, by omega⟩, -25373480160)]
  nu := [(⟨0, by omega⟩, -2858983680), (⟨3, by omega⟩, 2858983680), (⟨4, by omega⟩, 2858983680), (⟨5, by omega⟩, -4216012800), (⟨10, by omega⟩, -2858983680), (⟨11, by omega⟩, 924057600), (⟨12, by omega⟩, 2858983680), (⟨15, by omega⟩, -924057600), (⟨16, by omega⟩, -3537498240), (⟨20, by omega⟩, -2858983680), (⟨21, by omega⟩, 2858983680), (⟨22, by omega⟩, 2858983680), (⟨23, by omega⟩, 678514560), (⟨24, by omega⟩, 2858983680), (⟨25, by omega⟩, -2858983680), (⟨26, by omega⟩, -678514560), (⟨27, by omega⟩, -2858983680), (⟨28, by omega⟩, -678514560), (⟨29, by omega⟩, -2858983680), (⟨30, by omega⟩, -7399420160), (⟨31, by omega⟩, 4540436480), (⟨32, by omega⟩, 4540436480), (⟨33, by omega⟩, 7074996480), (⟨34, by omega⟩, 3183407360), (⟨35, by omega⟩, -4216012800), (⟨36, by omega⟩, -4216012800), (⟨37, by omega⟩, -324423680), (⟨38, by omega⟩, -4216012800), (⟨39, by omega⟩, -324423680), (⟨40, by omega⟩, -2858983680), (⟨41, by omega⟩, -678514560)]
  claimed := 185035296145903528389215846400
}
def branch_box_3143 : RatBox 8 := { lower := box_3143.profileLo, upper := box_3143.profileHi }
def accepted_3143 : Bool := checkAt 527 1000 box_3143 cert_3143

def box_3145 : Box := { S := 33856000, lo := ![0, 22641200, 1692800, 24968800, 33009600, 0, 32163200, 0], hi := ![846400, 23805000, 2539200, 26132600, 33856000, 846400, 33009600, 846400] }
def cert_3145 : Certificate := {
  mu := [(⟨4, by omega⟩, -7074200), (⟨5, by omega⟩, -19968000), (⟨6, by omega⟩, -13888000), (⟨9, by omega⟩, -19968000), (⟨14, by omega⟩, -4915200), (⟨21, by omega⟩, -12012800), (⟨30, by omega⟩, -4915200), (⟨33, by omega⟩, -13888000), (⟨37, by omega⟩, -19968000), (⟨41, by omega⟩, -18109952), (⟨45, by omega⟩, -3040000), (⟨49, by omega⟩, -19968000), (⟨53, by omega⟩, -13888000), (⟨61, by omega⟩, -3040000), (⟨70, by omega⟩, -13888000), (⟨74, by omega⟩, -18109952), (⟨82, by omega⟩, -19968000), (⟨86, by omega⟩, -13888000), (⟨90, by omega⟩, -36219904), (⟨94, by omega⟩, -6080000)]
  nu := [(⟨0, by omega⟩, -18109952), (⟨3, by omega⟩, 18109952), (⟨4, by omega⟩, 18109952), (⟨5, by omega⟩, -19968000), (⟨10, by omega⟩, -13888000), (⟨11, by omega⟩, 4915200), (⟨12, by omega⟩, 13888000), (⟨14, by omega⟩, 13888000), (⟨15, by omega⟩, -4915200), (⟨16, by omega⟩, -12012800), (⟨17, by omega⟩, -4915200), (⟨19, by omega⟩, -13888000), (⟨20, by omega⟩, -13888000), (⟨21, by omega⟩, 13888000), (⟨22, by omega⟩, 13888000), (⟨23, by omega⟩, 3040000), (⟨24, by omega⟩, 13888000), (⟨25, by omega⟩, -13888000), (⟨26, by omega⟩, -3040000), (⟨27, by omega⟩, -13888000), (⟨28, by omega⟩, -3040000), (⟨29, by omega⟩, -13888000), (⟨30, by omega⟩, -56187904), (⟨31, by omega⟩, 38077952), (⟨32, by omega⟩, 38077952), (⟨33, by omega⟩, 36219904), (⟨34, by omega⟩, 38077952), (⟨35, by omega⟩, -19968000), (⟨36, by omega⟩, -18109952), (⟨37, by omega⟩, -19968000), (⟨38, by omega⟩, -18109952), (⟨39, by omega⟩, -19968000), (⟨40, by omega⟩, -18109952), (⟨41, by omega⟩, -3040000)]
  claimed := 20082082195599360000000
}
def branch_box_3145 : RatBox 8 := { lower := box_3145.profileLo, upper := box_3145.profileHi }
def accepted_3145 : Bool := checkAt 527 1000 box_3145 cert_3145

def box_3149 : Box := { S := 1975173120, lo := ![0, 1320897024, 98758656, 1456690176, 1925793792, 0, 1925793792, 0], hi := ![49379328, 1354845312, 148137984, 1490638464, 1975173120, 49379328, 1975173120, 49379328] }
def cert_3149 : Certificate := {
  mu := [(⟨5, by omega⟩, -1882767360), (⟨6, by omega⟩, -92405760), (⟨9, by omega⟩, -1882767360), (⟨13, by omega⟩, -92405760), (⟨21, by omega⟩, -92405760), (⟨29, by omega⟩, -92405760), (⟨33, by omega⟩, -92405760), (⟨37, by omega⟩, -1882767360), (⟨41, by omega⟩, -10485760), (⟨45, by omega⟩, -92405760), (⟨53, by omega⟩, -92405760), (⟨61, by omega⟩, -92405760), (⟨69, by omega⟩, -92405760), (⟨73, by omega⟩, -10485760), (⟨77, by omega⟩, -92405760), (⟨85, by omega⟩, -92405760), (⟨89, by omega⟩, -184811520), (⟨93, by omega⟩, -1697955840), (⟨94, by omega⟩, -1697955840)]
  nu := [(⟨0, by omega⟩, -92405760), (⟨3, by omega⟩, 92405760), (⟨4, by omega⟩, 92405760), (⟨5, by omega⟩, -1882767360), (⟨10, by omega⟩, -92405760), (⟨11, by omega⟩, 92405760), (⟨12, by omega⟩, 92405760), (⟨13, by omega⟩, 92405760), (⟨14, by omega⟩, 92405760), (⟨15, by omega⟩, -92405760), (⟨16, by omega⟩, -92405760), (⟨17, by omega⟩, -92405760), (⟨18, by omega⟩, -92405760), (⟨19, by omega⟩, -92405760), (⟨20, by omega⟩, -92405760), (⟨21, by omega⟩, 92405760), (⟨22, by omega⟩, 92405760), (⟨23, by omega⟩, 92405760), (⟨24, by omega⟩, 92405760), (⟨25, by omega⟩, -92405760), (⟨26, by omega⟩, -92405760), (⟨27, by omega⟩, -92405760), (⟨28, by omega⟩, -92405760), (⟨29, by omega⟩, -92405760), (⟨30, by omega⟩, -102891520), (⟨31, by omega⟩, 10485760), (⟨32, by omega⟩, 10485760), (⟨33, by omega⟩, 102891520), (⟨34, by omega⟩, 92405760), (⟨35, by omega⟩, -1882767360), (⟨36, by omega⟩, -10485760), (⟨38, by omega⟩, -10485760), (⟨40, by omega⟩, -92405760), (⟨41, by omega⟩, -1697955840)]
  claimed := 4007134349570842832771481600
}
def branch_box_3149 : RatBox 8 := { lower := box_3149.profileLo, upper := box_3149.profileHi }
def accepted_3149 : Bool := checkAt 527 1000 box_3149 cert_3149

end PeaceableQueens.UpperBound.Generated.Even.Core
