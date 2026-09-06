import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_5 : Box := { S := 3694080, lo := ![0, 2216448, 0, 2216448, 3509376, 0, 3509376, 0], hi := ![369408, 2470416, 369408, 2724384, 3694080, 369408, 3694080, 369408] }
def cert_5 : Certificate := {
  mu := [(⟨5, by omega⟩, -3161600), (⟨6, by omega⟩, -532480), (⟨9, by omega⟩, -1763840), (⟨10, by omega⟩, -1397760), (⟨14, by omega⟩, -532480), (⟨21, by omega⟩, -2096640), (⟨29, by omega⟩, -532480), (⟨33, by omega⟩, -532480), (⟨38, by omega⟩, -3161600), (⟨41, by omega⟩, -131072), (⟨45, by omega⟩, -532480), (⟨53, by omega⟩, -532480), (⟨61, by omega⟩, -532480), (⟨69, by omega⟩, -2096640), (⟨73, by omega⟩, -131072), (⟨77, by omega⟩, -532480), (⟨85, by omega⟩, -532480), (⟨89, by omega⟩, -1064960), (⟨93, by omega⟩, -532480), (⟨94, by omega⟩, -532480)]
  nu := [(⟨0, by omega⟩, -532480), (⟨3, by omega⟩, 532480), (⟨4, by omega⟩, 532480), (⟨5, by omega⟩, -3161600), (⟨10, by omega⟩, -532480), (⟨11, by omega⟩, 532480), (⟨12, by omega⟩, 532480), (⟨13, by omega⟩, 532480), (⟨14, by omega⟩, 532480), (⟨15, by omega⟩, -532480), (⟨16, by omega⟩, -2096640), (⟨17, by omega⟩, -532480), (⟨18, by omega⟩, -532480), (⟨19, by omega⟩, -532480), (⟨20, by omega⟩, -532480), (⟨21, by omega⟩, 532480), (⟨22, by omega⟩, 532480), (⟨23, by omega⟩, 532480), (⟨24, by omega⟩, 532480), (⟨25, by omega⟩, -532480), (⟨26, by omega⟩, -532480), (⟨27, by omega⟩, -532480), (⟨28, by omega⟩, -532480), (⟨29, by omega⟩, -2096640), (⟨30, by omega⟩, -663552), (⟨31, by omega⟩, 131072), (⟨32, by omega⟩, 131072), (⟨33, by omega⟩, 663552), (⟨34, by omega⟩, 532480), (⟨35, by omega⟩, -3161600), (⟨36, by omega⟩, -131072), (⟨38, by omega⟩, -131072), (⟨40, by omega⟩, -532480), (⟨41, by omega⟩, -532480)]
  claimed := 25593103084938854400
}
def branch_box_5 : RatBox 8 := { lower := box_5.profileLo, upper := box_5.profileHi }
def accepted_5 : Bool := checkAt 527 1000 box_5 cert_5

def box_7 : Box := { S := 15808000, lo := ![0, 10571600, 0, 9484800, 15017600, 0, 15017600, 0], hi := ![1580800, 11658400, 1580800, 10571600, 15808000, 1580800, 15808000, 1580800] }
def cert_7 : Certificate := {
  mu := [(⟨3, by omega⟩, -2321280), (⟨5, by omega⟩, -14476800), (⟨6, by omega⟩, -1331200), (⟨10, by omega⟩, -14476800), (⟨14, by omega⟩, -1331200), (⟨22, by omega⟩, -11814400), (⟨30, by omega⟩, -1331200), (⟨33, by omega⟩, -1331200), (⟨38, by omega⟩, -14476800), (⟨41, by omega⟩, -327680), (⟨45, by omega⟩, -1331200), (⟨53, by omega⟩, -1331200), (⟨61, by omega⟩, -5241600), (⟨69, by omega⟩, -7904000), (⟨73, by omega⟩, -327680), (⟨77, by omega⟩, -1331200), (⟨85, by omega⟩, -1331200), (⟨89, by omega⟩, -2662400), (⟨94, by omega⟩, -2662400)]
  nu := [(⟨0, by omega⟩, -1331200), (⟨3, by omega⟩, 1331200), (⟨4, by omega⟩, 1331200), (⟨5, by omega⟩, -14476800), (⟨10, by omega⟩, -1331200), (⟨11, by omega⟩, 1331200), (⟨12, by omega⟩, 1331200), (⟨13, by omega⟩, 1331200), (⟨14, by omega⟩, 1331200), (⟨15, by omega⟩, -1331200), (⟨16, by omega⟩, -11814400), (⟨17, by omega⟩, -1331200), (⟨18, by omega⟩, -1331200), (⟨19, by omega⟩, -1331200), (⟨20, by omega⟩, -1331200), (⟨21, by omega⟩, 1331200), (⟨22, by omega⟩, 1331200), (⟨23, by omega⟩, 1331200), (⟨24, by omega⟩, 1331200), (⟨25, by omega⟩, -1331200), (⟨26, by omega⟩, -1331200), (⟨27, by omega⟩, -1331200), (⟨28, by omega⟩, -5241600), (⟨29, by omega⟩, -7904000), (⟨30, by omega⟩, -1658880), (⟨31, by omega⟩, 327680), (⟨32, by omega⟩, 327680), (⟨33, by omega⟩, 1658880), (⟨34, by omega⟩, 1331200), (⟨35, by omega⟩, -14476800), (⟨36, by omega⟩, -327680), (⟨38, by omega⟩, -327680), (⟨40, by omega⟩, -1331200), (⟨41, by omega⟩, -1331200)]
  claimed := 1991146090459136000000
}
def branch_box_7 : RatBox 8 := { lower := box_7.profileLo, upper := box_7.profileHi }
def accepted_7 : Bool := checkAt 527 1000 box_7 cert_7

def box_14 : Box := { S := 224719200, lo := ![0, 150280965, 0, 150280965, 213483240, 11235960, 213483240, 0], hi := ![11235960, 165730410, 11235960, 165730410, 224719200, 22471920, 224719200, 22471920] }
def cert_14 : Certificate := {
  mu := [(⟨4, by omega⟩, -40621500), (⟨5, by omega⟩, -129139200), (⟨6, by omega⟩, -95580000), (⟨9, by omega⟩, -129139200), (⟨14, by omega⟩, -16779600), (⟨21, by omega⟩, -16779600), (⟨30, by omega⟩, -16779600), (⟨33, by omega⟩, -57395200), (⟨37, by omega⟩, -64569600), (⟨38, by omega⟩, -64569600), (⟨42, by omega⟩, -129139200), (⟨45, by omega⟩, -95580000), (⟨53, by omega⟩, -95580000), (⟨61, by omega⟩, -57395200), (⟨70, by omega⟩, -57395200), (⟨74, by omega⟩, -129139200), (⟨77, by omega⟩, -95580000), (⟨80, by omega⟩, -46137600), (⟨85, by omega⟩, -95580000), (⟨89, by omega⟩, -59259600), (⟨90, by omega⟩, -131900400), (⟨94, by omega⟩, -191160000)]
  nu := [(⟨0, by omega⟩, -95580000), (⟨3, by omega⟩, 95580000), (⟨4, by omega⟩, 95580000), (⟨5, by omega⟩, -129139200), (⟨10, by omega⟩, -95580000), (⟨11, by omega⟩, 16779600), (⟨12, by omega⟩, 95580000), (⟨13, by omega⟩, 95580000), (⟨14, by omega⟩, 95580000), (⟨15, by omega⟩, -16779600), (⟨16, by omega⟩, -16779600), (⟨17, by omega⟩, -16779600), (⟨18, by omega⟩, -95580000), (⟨19, by omega⟩, -95580000), (⟨20, by omega⟩, -95580000), (⟨21, by omega⟩, 95580000), (⟨22, by omega⟩, 57395200), (⟨23, by omega⟩, 95580000), (⟨24, by omega⟩, 95580000), (⟨25, by omega⟩, -57395200), (⟨26, by omega⟩, -95580000), (⟨27, by omega⟩, -95580000), (⟨28, by omega⟩, -57395200), (⟨29, by omega⟩, -57395200), (⟨30, by omega⟩, -224719200), (⟨31, by omega⟩, 129139200), (⟨32, by omega⟩, 83001600), (⟨33, by omega⟩, 224719200), (⟨34, by omega⟩, 95580000), (⟨35, by omega⟩, -129139200), (⟨36, by omega⟩, -129139200), (⟨38, by omega⟩, -129139200), (⟨39, by omega⟩, 46137600), (⟨40, by omega⟩, -95580000), (⟨41, by omega⟩, -95580000)]
  claimed := 5851744475374436267520000
}
def branch_box_14 : RatBox 8 := { lower := box_14.profileLo, upper := box_14.profileHi }
def accepted_14 : Bool := checkAt 527 1000 box_14 cert_14

def box_16 : Box := { S := 1269600, lo := ![0, 849045, 0, 849045, 1206120, 0, 1206120, 63480], hi := ![63480, 936330, 63480, 936330, 1269600, 63480, 1269600, 126960] }
def cert_16 : Certificate := {
  mu := [(⟨5, by omega⟩, -729600), (⟨6, by omega⟩, -540000), (⟨9, by omega⟩, -729600), (⟨14, by omega⟩, -540000), (⟨22, by omega⟩, -189600), (⟨29, by omega⟩, -540000), (⟨33, by omega⟩, -540000), (⟨37, by omega⟩, -364800), (⟨38, by omega⟩, -364800), (⟨42, by omega⟩, -160000), (⟨53, by omega⟩, -540000), (⟨69, by omega⟩, -729600), (⟨74, by omega⟩, -160000), (⟨85, by omega⟩, -540000), (⟨89, by omega⟩, -1080000)]
  nu := [(⟨0, by omega⟩, -540000), (⟨3, by omega⟩, 540000), (⟨4, by omega⟩, 540000), (⟨5, by omega⟩, -729600), (⟨10, by omega⟩, -540000), (⟨11, by omega⟩, 540000), (⟨12, by omega⟩, 540000), (⟨14, by omega⟩, 540000), (⟨15, by omega⟩, -540000), (⟨16, by omega⟩, -189600), (⟨17, by omega⟩, -540000), (⟨19, by omega⟩, -540000), (⟨20, by omega⟩, -540000), (⟨21, by omega⟩, 540000), (⟨22, by omega⟩, 540000), (⟨24, by omega⟩, 540000), (⟨25, by omega⟩, -540000), (⟨27, by omega⟩, -540000), (⟨29, by omega⟩, -729600), (⟨30, by omega⟩, -700000), (⟨31, by omega⟩, 160000), (⟨32, by omega⟩, 160000), (⟨33, by omega⟩, 700000), (⟨34, by omega⟩, 540000), (⟨35, by omega⟩, -729600), (⟨36, by omega⟩, -160000), (⟨38, by omega⟩, -160000), (⟨40, by omega⟩, -540000)]
  claimed := 1073771140141440000
}
def branch_box_16 : RatBox 8 := { lower := box_16.profileLo, upper := box_16.profileHi }
def accepted_16 : Bool := checkAt 527 1000 box_16 cert_16

def box_17 : Box := { S := 140774400, lo := ![0, 94142880, 0, 94142880, 133735680, 0, 133735680, 0], hi := ![7038720, 98982000, 7038720, 103821120, 140774400, 7038720, 140774400, 7038720] }
def cert_17 : Certificate := {
  mu := [(⟨5, by omega⟩, -129223680), (⟨6, by omega⟩, -11550720), (⟨9, by omega⟩, -68582400), (⟨10, by omega⟩, -60641280), (⟨14, by omega⟩, -11550720), (⟨21, by omega⟩, -11550720), (⟨29, by omega⟩, -106122240), (⟨33, by omega⟩, -11550720), (⟨37, by omega⟩, -129223680), (⟨41, by omega⟩, -2621440), (⟨45, by omega⟩, -11550720), (⟨53, by omega⟩, -11550720), (⟨61, by omega⟩, -94571520), (⟨69, by omega⟩, -23101440), (⟨73, by omega⟩, -2621440), (⟨77, by omega⟩, -11550720), (⟨85, by omega⟩, -11550720), (⟨89, by omega⟩, -23101440), (⟨94, by omega⟩, -23101440)]
  nu := [(⟨0, by omega⟩, -11550720), (⟨3, by omega⟩, 11550720), (⟨4, by omega⟩, 11550720), (⟨5, by omega⟩, -129223680), (⟨10, by omega⟩, -11550720), (⟨11, by omega⟩, 11550720), (⟨12, by omega⟩, 11550720), (⟨13, by omega⟩, 11550720), (⟨14, by omega⟩, 11550720), (⟨15, by omega⟩, -11550720), (⟨16, by omega⟩, -11550720), (⟨17, by omega⟩, -106122240), (⟨18, by omega⟩, -11550720), (⟨19, by omega⟩, -11550720), (⟨20, by omega⟩, -11550720), (⟨21, by omega⟩, 11550720), (⟨22, by omega⟩, 11550720), (⟨23, by omega⟩, 11550720), (⟨24, by omega⟩, 11550720), (⟨25, by omega⟩, -11550720), (⟨26, by omega⟩, -11550720), (⟨27, by omega⟩, -11550720), (⟨28, by omega⟩, -94571520), (⟨29, by omega⟩, -23101440), (⟨30, by omega⟩, -14172160), (⟨31, by omega⟩, 2621440), (⟨32, by omega⟩, 2621440), (⟨33, by omega⟩, 14172160), (⟨34, by omega⟩, 11550720), (⟨35, by omega⟩, -129223680), (⟨36, by omega⟩, -2621440), (⟨38, by omega⟩, -2621440), (⟨40, by omega⟩, -11550720), (⟨41, by omega⟩, -11550720)]
  claimed := 1456001153565805117440000
}
def branch_box_17 : RatBox 8 := { lower := box_17.profileLo, upper := box_17.profileHi }
def accepted_17 : Bool := checkAt 527 1000 box_17 cert_17

def box_19 : Box := { S := 646118400, lo := ![0, 454302000, 0, 432091680, 613812480, 0, 613812480, 0], hi := ![32305920, 476512320, 32305920, 454302000, 646118400, 32305920, 646118400, 32305920] }
def cert_19 : Certificate := {
  mu := [(⟨3, by omega⟩, -51707520), (⟨5, by omega⟩, -617241600), (⟨6, by omega⟩, -28876800), (⟨10, by omega⟩, -617241600), (⟨14, by omega⟩, -28876800), (⟨22, by omega⟩, -559488000), (⟨30, by omega⟩, -28876800), (⟨33, by omega⟩, -28876800), (⟨37, by omega⟩, -617241600), (⟨41, by omega⟩, -6553600), (⟨45, by omega⟩, -28876800), (⟨53, by omega⟩, -28876800), (⟨61, by omega⟩, -323059200), (⟨69, by omega⟩, -265305600), (⟨73, by omega⟩, -6553600), (⟨77, by omega⟩, -28876800), (⟨85, by omega⟩, -28876800), (⟨89, by omega⟩, -57753600), (⟨93, by omega⟩, -57753600)]
  nu := [(⟨0, by omega⟩, -28876800), (⟨3, by omega⟩, 28876800), (⟨4, by omega⟩, 28876800), (⟨5, by omega⟩, -617241600), (⟨10, by omega⟩, -28876800), (⟨11, by omega⟩, 28876800), (⟨12, by omega⟩, 28876800), (⟨13, by omega⟩, 28876800), (⟨14, by omega⟩, 28876800), (⟨15, by omega⟩, -28876800), (⟨16, by omega⟩, -559488000), (⟨17, by omega⟩, -28876800), (⟨18, by omega⟩, -28876800), (⟨19, by omega⟩, -28876800), (⟨20, by omega⟩, -28876800), (⟨21, by omega⟩, 28876800), (⟨22, by omega⟩, 28876800), (⟨23, by omega⟩, 28876800), (⟨24, by omega⟩, 28876800), (⟨25, by omega⟩, -28876800), (⟨26, by omega⟩, -28876800), (⟨27, by omega⟩, -28876800), (⟨28, by omega⟩, -323059200), (⟨29, by omega⟩, -265305600), (⟨30, by omega⟩, -35430400), (⟨31, by omega⟩, 6553600), (⟨32, by omega⟩, 6553600), (⟨33, by omega⟩, 35430400), (⟨34, by omega⟩, 28876800), (⟨35, by omega⟩, -617241600), (⟨36, by omega⟩, -6553600), (⟨38, by omega⟩, -6553600), (⟨40, by omega⟩, -28876800), (⟨41, by omega⟩, -28876800)]
  claimed := 140543191667279951953920000
}
def branch_box_19 : RatBox 8 := { lower := box_19.profileLo, upper := box_19.profileHi }
def accepted_19 : Bool := checkAt 527 1000 box_19 cert_19

def box_24 : Box := { S := 67704000, lo := ![0, 47604375, 0, 47604375, 64318800, 1692600, 64318800, 0], hi := ![1692600, 49931700, 3385200, 49931700, 67704000, 3385200, 67704000, 3385200] }
def cert_24 : Certificate := {
  mu := [(⟨3, by omega⟩, -669240), (⟨4, by omega⟩, -13664040), (⟨5, by omega⟩, -38937600), (⟨6, by omega⟩, -28766400), (⟨9, by omega⟩, -38522640), (⟨18, by omega⟩, -414960), (⟨21, by omega⟩, -10171200), (⟨33, by omega⟩, -8705632), (⟨38, by omega⟩, -38937600), (⟨42, by omega⟩, -37352064), (⟨45, by omega⟩, -28766400), (⟨53, by omega⟩, -28766400), (⟨61, by omega⟩, -8705632), (⟨66, by omega⟩, -13664040), (⟨70, by omega⟩, -8705632), (⟨74, by omega⟩, -37352064), (⟨77, by omega⟩, -28766400), (⟨85, by omega⟩, -28766400), (⟨89, by omega⟩, -30204720), (⟨94, by omega⟩, -57532800)]
  nu := [(⟨0, by omega⟩, -28766400), (⟨2, by omega⟩, 13664040), (⟨3, by omega⟩, 15102360), (⟨4, by omega⟩, 28766400), (⟨5, by omega⟩, -38522640), (⟨6, by omega⟩, -414960), (⟨9, by omega⟩, -13664040), (⟨10, by omega⟩, -28766400), (⟨12, by omega⟩, 28766400), (⟨13, by omega⟩, 28766400), (⟨14, by omega⟩, 28766400), (⟨16, by omega⟩, -10171200), (⟨18, by omega⟩, -28766400), (⟨19, by omega⟩, -28766400), (⟨20, by omega⟩, -28766400), (⟨21, by omega⟩, 28766400), (⟨22, by omega⟩, 8705632), (⟨23, by omega⟩, 28766400), (⟨24, by omega⟩, 28766400), (⟨25, by omega⟩, -8705632), (⟨26, by omega⟩, -28766400), (⟨27, by omega⟩, -28766400), (⟨28, by omega⟩, -8705632), (⟨29, by omega⟩, -8705632), (⟨30, by omega⟩, -52454424), (⟨31, by omega⟩, 37352064), (⟨32, by omega⟩, 37352064), (⟨33, by omega⟩, 52454424), (⟨34, by omega⟩, 15102360), (⟨35, by omega⟩, -38937600), (⟨36, by omega⟩, -37352064), (⟨38, by omega⟩, -37352064), (⟨40, by omega⟩, -15102360), (⟨41, by omega⟩, -28766400)]
  claimed := 163008404730872064000000
}
def branch_box_24 : RatBox 8 := { lower := box_24.profileLo, upper := box_24.profileHi }
def accepted_24 : Bool := checkAt 527 1000 box_24 cert_24

def box_29 : Box := { S := 428800, lo := ![0, 301500, 0, 301500, 407360, 0, 407360, 0], hi := ![10720, 316240, 21440, 316240, 418080, 10720, 418080, 10720] }
def cert_29 : Certificate := {
  mu := [(⟨4, by omega⟩, -4800), (⟨5, by omega⟩, -403200), (⟨6, by omega⟩, -25600), (⟨9, by omega⟩, -268800), (⟨10, by omega⟩, -134400), (⟨14, by omega⟩, -25600), (⟨21, by omega⟩, -243200), (⟨29, by omega⟩, -25600), (⟨33, by omega⟩, -25600), (⟨37, by omega⟩, -403200), (⟨41, by omega⟩, -403200), (⟨45, by omega⟩, -25600), (⟨49, by omega⟩, -403200), (⟨53, by omega⟩, -25600), (⟨61, by omega⟩, -243200), (⟨69, by omega⟩, -25600), (⟨73, by omega⟩, -403200), (⟨77, by omega⟩, -25600), (⟨81, by omega⟩, -403200), (⟨85, by omega⟩, -25600), (⟨89, by omega⟩, -806400), (⟨93, by omega⟩, -268800)]
  nu := [(⟨0, by omega⟩, -403200), (⟨3, by omega⟩, 403200), (⟨4, by omega⟩, 403200), (⟨5, by omega⟩, -403200), (⟨10, by omega⟩, -25600), (⟨11, by omega⟩, 25600), (⟨12, by omega⟩, 25600), (⟨13, by omega⟩, 25600), (⟨14, by omega⟩, 25600), (⟨15, by omega⟩, -25600), (⟨16, by omega⟩, -243200), (⟨17, by omega⟩, -25600), (⟨18, by omega⟩, -25600), (⟨19, by omega⟩, -25600), (⟨20, by omega⟩, -25600), (⟨21, by omega⟩, 25600), (⟨22, by omega⟩, 25600), (⟨23, by omega⟩, 25600), (⟨24, by omega⟩, 25600), (⟨25, by omega⟩, -25600), (⟨26, by omega⟩, -25600), (⟨27, by omega⟩, -25600), (⟨28, by omega⟩, -243200), (⟨29, by omega⟩, -25600), (⟨30, by omega⟩, -1209600), (⟨31, by omega⟩, 806400), (⟨32, by omega⟩, 806400), (⟨33, by omega⟩, 806400), (⟨34, by omega⟩, 806400), (⟨35, by omega⟩, -403200), (⟨36, by omega⟩, -403200), (⟨37, by omega⟩, -403200), (⟨38, by omega⟩, -403200), (⟨39, by omega⟩, -403200), (⟨40, by omega⟩, -403200), (⟨41, by omega⟩, -134400)]
  claimed := 41126261514240000
}
def branch_box_29 : RatBox 8 := { lower := box_29.profileLo, upper := box_29.profileHi }
def accepted_29 : Bool := checkAt 527 1000 box_29 cert_29

def box_31 : Box := { S := 1041111040, lo := ![0, 732031200, 0, 732031200, 989055488, 0, 1015083264, 0], hi := ![26027776, 749925296, 52055552, 767819392, 1015083264, 26027776, 1041111040, 26027776] }
def cert_31 : Certificate := {
  mu := [(⟨5, by omega⟩, -993105920), (⟨6, by omega⟩, -48005120), (⟨9, by omega⟩, -708075520), (⟨10, by omega⟩, -285030400), (⟨13, by omega⟩, -48005120), (⟨21, by omega⟩, -48005120), (⟨29, by omega⟩, -48005120), (⟨34, by omega⟩, -48005120), (⟨37, by omega⟩, -993105920), (⟨41, by omega⟩, -993105920), (⟨45, by omega⟩, -48005120), (⟨49, by omega⟩, -10485760), (⟨53, by omega⟩, -48005120), (⟨61, by omega⟩, -48005120), (⟨68, by omega⟩, -138014720), (⟨69, by omega⟩, -186019840), (⟨73, by omega⟩, -993105920), (⟨77, by omega⟩, -48005120), (⟨81, by omega⟩, -10485760), (⟨85, by omega⟩, -48005120), (⟨90, by omega⟩, -96010240), (⟨93, by omega⟩, -897095680), (⟨94, by omega⟩, -897095680)]
  nu := [(⟨0, by omega⟩, -48005120), (⟨3, by omega⟩, 48005120), (⟨4, by omega⟩, 48005120), (⟨5, by omega⟩, -993105920), (⟨10, by omega⟩, -48005120), (⟨11, by omega⟩, 48005120), (⟨12, by omega⟩, 48005120), (⟨13, by omega⟩, 48005120), (⟨14, by omega⟩, 48005120), (⟨15, by omega⟩, -48005120), (⟨16, by omega⟩, -48005120), (⟨17, by omega⟩, -48005120), (⟨18, by omega⟩, -48005120), (⟨19, by omega⟩, -48005120), (⟨20, by omega⟩, -48005120), (⟨21, by omega⟩, 48005120), (⟨22, by omega⟩, 48005120), (⟨23, by omega⟩, 48005120), (⟨24, by omega⟩, 48005120), (⟨25, by omega⟩, -48005120), (⟨26, by omega⟩, -48005120), (⟨27, by omega⟩, -48005120), (⟨28, by omega⟩, -48005120), (⟨29, by omega⟩, -48005120), (⟨30, by omega⟩, -1051596800), (⟨31, by omega⟩, 1003591680), (⟨32, by omega⟩, 1003591680), (⟨33, by omega⟩, 1041111040), (⟨34, by omega⟩, 58490880), (⟨35, by omega⟩, -993105920), (⟨36, by omega⟩, -993105920), (⟨37, by omega⟩, -10485760), (⟨38, by omega⟩, -993105920), (⟨39, by omega⟩, -10485760), (⟨40, by omega⟩, -48005120), (⟨41, by omega⟩, -897095680)]
  claimed := 588005587158629569422950400
}
def branch_box_31 : RatBox 8 := { lower := box_31.profileLo, upper := box_31.profileHi }
def accepted_31 : Bool := checkAt 527 1000 box_31 cert_31

def box_33 : Box := { S := 5205555200, lo := ![0, 3749626480, 0, 3660156000, 4945277440, 0, 5075416320, 0], hi := ![130138880, 3839096960, 260277760, 3749626480, 5075416320, 130138880, 5205555200, 130138880] }
def cert_33 : Certificate := {
  mu := [(⟨5, by omega⟩, -4965529600), (⟨6, by omega⟩, -240025600), (⟨9, by omega⟩, -3540377600), (⟨10, by omega⟩, -1425152000), (⟨13, by omega⟩, -240025600), (⟨21, by omega⟩, -240025600), (⟨29, by omega⟩, -240025600), (⟨34, by omega⟩, -240025600), (⟨37, by omega⟩, -4965529600), (⟨41, by omega⟩, -4965529600), (⟨45, by omega⟩, -240025600), (⟨49, by omega⟩, -52428800), (⟨53, by omega⟩, -240025600), (⟨61, by omega⟩, -240025600), (⟨68, by omega⟩, -855091200), (⟨69, by omega⟩, -1095116800), (⟨73, by omega⟩, -4965529600), (⟨77, by omega⟩, -240025600), (⟨81, by omega⟩, -52428800), (⟨85, by omega⟩, -240025600), (⟨90, by omega⟩, -480051200), (⟨93, by omega⟩, -4485478400), (⟨94, by omega⟩, -4485478400)]
  nu := [(⟨0, by omega⟩, -240025600), (⟨3, by omega⟩, 240025600), (⟨4, by omega⟩, 240025600), (⟨5, by omega⟩, -4965529600), (⟨10, by omega⟩, -240025600), (⟨11, by omega⟩, 240025600), (⟨12, by omega⟩, 240025600), (⟨13, by omega⟩, 240025600), (⟨14, by omega⟩, 240025600), (⟨15, by omega⟩, -240025600), (⟨16, by omega⟩, -240025600), (⟨17, by omega⟩, -240025600), (⟨18, by omega⟩, -240025600), (⟨19, by omega⟩, -240025600), (⟨20, by omega⟩, -240025600), (⟨21, by omega⟩, 240025600), (⟨22, by omega⟩, 240025600), (⟨23, by omega⟩, 240025600), (⟨24, by omega⟩, 240025600), (⟨25, by omega⟩, -240025600), (⟨26, by omega⟩, -240025600), (⟨27, by omega⟩, -240025600), (⟨28, by omega⟩, -240025600), (⟨29, by omega⟩, -240025600), (⟨30, by omega⟩, -5257984000), (⟨31, by omega⟩, 5017958400), (⟨32, by omega⟩, 5017958400), (⟨33, by omega⟩, 5205555200), (⟨34, by omega⟩, 292454400), (⟨35, by omega⟩, -4965529600), (⟨36, by omega⟩, -4965529600), (⟨37, by omega⟩, -52428800), (⟨38, by omega⟩, -4965529600), (⟨39, by omega⟩, -52428800), (⟨40, by omega⟩, -240025600), (⟨41, by omega⟩, -4485478400)]
  claimed := 73503493154039013496586240000
}
def branch_box_33 : RatBox 8 := { lower := box_33.profileLo, upper := box_33.profileHi }
def accepted_33 : Bool := checkAt 527 1000 box_33 cert_33

def box_36 : Box := { S := 976848000, lo := ![0, 703635825, 0, 703635825, 928005600, 12210600, 952426800, 0], hi := ![24421200, 720425400, 48842400, 720425400, 952426800, 24421200, 976848000, 24421200] }
def cert_36 : Certificate := {
  mu := [(⟨5, by omega⟩, -570316800), (⟨6, by omega⟩, -406531200), (⟨9, by omega⟩, -570316800), (⟨14, by omega⟩, -81892800), (⟨21, by omega⟩, -81892800), (⟨30, by omega⟩, -81892800), (⟨33, by omega⟩, -65220960), (⟨37, by omega⟩, -285158400), (⟨38, by omega⟩, -285158400), (⟨42, by omega⟩, -570316800), (⟨45, by omega⟩, -406531200), (⟨50, by omega⟩, -46131200), (⟨53, by omega⟩, -406531200), (⟨61, by omega⟩, -98564640), (⟨70, by omega⟩, -65220960), (⟨74, by omega⟩, -570316800), (⟨77, by omega⟩, -406531200), (⟨82, by omega⟩, -46131200), (⟨85, by omega⟩, -406531200), (⟨89, by omega⟩, -813062400), (⟨94, by omega⟩, -813062400)]
  nu := [(⟨0, by omega⟩, -406531200), (⟨3, by omega⟩, 406531200), (⟨4, by omega⟩, 406531200), (⟨5, by omega⟩, -570316800), (⟨10, by omega⟩, -406531200), (⟨11, by omega⟩, 81892800), (⟨12, by omega⟩, 406531200), (⟨13, by omega⟩, 406531200), (⟨14, by omega⟩, 406531200), (⟨15, by omega⟩, -81892800), (⟨16, by omega⟩, -81892800), (⟨17, by omega⟩, -81892800), (⟨18, by omega⟩, -406531200), (⟨19, by omega⟩, -406531200), (⟨20, by omega⟩, -406531200), (⟨21, by omega⟩, 406531200), (⟨22, by omega⟩, 65220960), (⟨23, by omega⟩, 406531200), (⟨24, by omega⟩, 406531200), (⟨25, by omega⟩, -65220960), (⟨26, by omega⟩, -406531200), (⟨27, by omega⟩, -406531200), (⟨28, by omega⟩, -98564640), (⟨29, by omega⟩, -65220960), (⟨30, by omega⟩, -1022979200), (⟨31, by omega⟩, 616448000), (⟨32, by omega⟩, 616448000), (⟨33, by omega⟩, 976848000), (⟨34, by omega⟩, 452662400), (⟨35, by omega⟩, -570316800), (⟨36, by omega⟩, -570316800), (⟨37, by omega⟩, -46131200), (⟨38, by omega⟩, -570316800), (⟨39, by omega⟩, -46131200), (⟨40, by omega⟩, -406531200), (⟨41, by omega⟩, -406531200)]
  claimed := 490654058804214172416000000
}
def branch_box_36 : RatBox 8 := { lower := box_36.profileLo, upper := box_36.profileHi }
def accepted_36 : Bool := checkAt 527 1000 box_36 cert_36

def box_37 : Box := { S := 455862400, lo := ![0, 328363385, 0, 328363385, 433069280, 0, 444465840, 0], hi := ![11396560, 336198520, 22793120, 336198520, 438767560, 5698280, 455862400, 11396560] }
def cert_37 : Certificate := {
  mu := [(⟨5, by omega⟩, -269516800), (⟨6, by omega⟩, -186345600), (⟨9, by omega⟩, -269516800), (⟨21, by omega⟩, -269516800), (⟨33, by omega⟩, -38502400), (⟨37, by omega⟩, -134758400), (⟨38, by omega⟩, -134758400), (⟨42, by omega⟩, -269516800), (⟨45, by omega⟩, -186345600), (⟨50, by omega⟩, -42291200), (⟨62, by omega⟩, -269516800), (⟨74, by omega⟩, -269516800), (⟨77, by omega⟩, -186345600), (⟨82, by omega⟩, -42291200), (⟨90, by omega⟩, -372691200)]
  nu := [(⟨0, by omega⟩, -186345600), (⟨3, by omega⟩, 186345600), (⟨4, by omega⟩, 186345600), (⟨5, by omega⟩, -269516800), (⟨10, by omega⟩, -186345600), (⟨12, by omega⟩, 186345600), (⟨13, by omega⟩, 186345600), (⟨16, by omega⟩, -269516800), (⟨18, by omega⟩, -186345600), (⟨20, by omega⟩, -186345600), (⟨21, by omega⟩, 186345600), (⟨22, by omega⟩, 38502400), (⟨23, by omega⟩, 186345600), (⟨25, by omega⟩, -38502400), (⟨26, by omega⟩, -186345600), (⟨28, by omega⟩, -269516800), (⟨30, by omega⟩, -498153600), (⟨31, by omega⟩, 311808000), (⟨32, by omega⟩, 311808000), (⟨33, by omega⟩, 455862400), (⟨34, by omega⟩, 228636800), (⟨35, by omega⟩, -269516800), (⟨36, by omega⟩, -269516800), (⟨37, by omega⟩, -42291200), (⟨38, by omega⟩, -269516800), (⟨39, by omega⟩, -42291200), (⟨40, by omega⟩, -186345600)]
  claimed := 49796087325546125885440000
}
def branch_box_37 : RatBox 8 := { lower := box_37.profileLo, upper := box_37.profileHi }
def accepted_37 : Bool := checkAt 527 1000 box_37 cert_37

def box_39 : Box := { S := 29097600, lo := ![0, 20959365, 0, 20959365, 28006440, 0, 28370160, 0], hi := ![727440, 21459480, 1454880, 21459480, 28370160, 363720, 28733880, 727440] }
def cert_39 : Certificate := {
  mu := [(⟨3, by omega⟩, -147840), (⟨5, by omega⟩, -17203200), (⟨6, by omega⟩, -11894400), (⟨10, by omega⟩, -17203200), (⟨14, by omega⟩, -2713600), (⟨21, by omega⟩, -14450688), (⟨33, by omega⟩, -11894400), (⟨38, by omega⟩, -17203200), (⟨42, by omega⟩, -17203200), (⟨50, by omega⟩, -17203200), (⟨69, by omega⟩, -14450688), (⟨74, by omega⟩, -17203200), (⟨77, by omega⟩, -11894400), (⟨82, by omega⟩, -17203200), (⟨85, by omega⟩, -2752512), (⟨89, by omega⟩, -34406400), (⟨94, by omega⟩, -5505024)]
  nu := [(⟨0, by omega⟩, -17203200), (⟨3, by omega⟩, 17203200), (⟨4, by omega⟩, 17203200), (⟨5, by omega⟩, -17203200), (⟨10, by omega⟩, -11894400), (⟨11, by omega⟩, 2713600), (⟨12, by omega⟩, 11894400), (⟨13, by omega⟩, 11894400), (⟨14, by omega⟩, 2752512), (⟨15, by omega⟩, -2713600), (⟨16, by omega⟩, -14450688), (⟨18, by omega⟩, -11894400), (⟨19, by omega⟩, -2752512), (⟨20, by omega⟩, -11894400), (⟨21, by omega⟩, 11894400), (⟨22, by omega⟩, 11894400), (⟨25, by omega⟩, -11894400), (⟨29, by omega⟩, -14450688), (⟨30, by omega⟩, -51609600), (⟨31, by omega⟩, 34406400), (⟨32, by omega⟩, 34406400), (⟨33, by omega⟩, 34406400), (⟨34, by omega⟩, 34406400), (⟨35, by omega⟩, -17203200), (⟨36, by omega⟩, -17203200), (⟨37, by omega⟩, -17203200), (⟨38, by omega⟩, -17203200), (⟨39, by omega⟩, -17203200), (⟨40, by omega⟩, -17203200), (⟨41, by omega⟩, -2752512)]
  claimed := 12958973445380014080000
}
def branch_box_39 : RatBox 8 := { lower := box_39.profileLo, upper := box_39.profileHi }
def accepted_39 : Bool := checkAt 527 1000 box_39 cert_39

def box_43 : Box := { S := 29097600, lo := ![0, 20959365, 0, 20959365, 28006440, 0, 28733880, 0], hi := ![727440, 21459480, 1454880, 21459480, 28188300, 363720, 28915740, 727440] }
def cert_43 : Certificate := {
  mu := [(⟨5, by omega⟩, -17203200), (⟨6, by omega⟩, -11894400), (⟨10, by omega⟩, -17203200), (⟨14, by omega⟩, -3276800), (⟨21, by omega⟩, -17203200), (⟨33, by omega⟩, -819200), (⟨37, by omega⟩, -8601600), (⟨38, by omega⟩, -8601600), (⟨42, by omega⟩, -17203200), (⟨45, by omega⟩, -11894400), (⟨50, by omega⟩, -17203200), (⟨62, by omega⟩, -17203200), (⟨74, by omega⟩, -17203200), (⟨77, by omega⟩, -11894400), (⟨82, by omega⟩, -17203200), (⟨89, by omega⟩, -34406400)]
  nu := [(⟨0, by omega⟩, -17203200), (⟨3, by omega⟩, 17203200), (⟨4, by omega⟩, 17203200), (⟨5, by omega⟩, -17203200), (⟨10, by omega⟩, -11894400), (⟨11, by omega⟩, 3276800), (⟨12, by omega⟩, 11894400), (⟨13, by omega⟩, 11894400), (⟨15, by omega⟩, -3276800), (⟨16, by omega⟩, -17203200), (⟨18, by omega⟩, -11894400), (⟨20, by omega⟩, -11894400), (⟨21, by omega⟩, 11894400), (⟨22, by omega⟩, 819200), (⟨23, by omega⟩, 11894400), (⟨25, by omega⟩, -819200), (⟨26, by omega⟩, -11894400), (⟨28, by omega⟩, -17203200), (⟨30, by omega⟩, -51609600), (⟨31, by omega⟩, 34406400), (⟨32, by omega⟩, 34406400), (⟨33, by omega⟩, 34406400), (⟨34, by omega⟩, 34406400), (⟨35, by omega⟩, -17203200), (⟨36, by omega⟩, -17203200), (⟨37, by omega⟩, -17203200), (⟨38, by omega⟩, -17203200), (⟨39, by omega⟩, -17203200), (⟨40, by omega⟩, -17203200)]
  claimed := 12955559670626549760000
}
def branch_box_43 : RatBox 8 := { lower := box_43.profileLo, upper := box_43.profileHi }
def accepted_43 : Bool := checkAt 527 1000 box_43 cert_43

def box_45 : Box := { S := 1370113920, lo := ![0, 986910183, 0, 986910183, 1318734648, 0, 1361550708, 0], hi := ![34252848, 1010459016, 68505696, 1010459016, 1323016254, 17126424, 1370113920, 34252848] }
def cert_45 : Certificate := {
  mu := [(⟨5, by omega⟩, -808550400), (⟨6, by omega⟩, -561563520), (⟨9, by omega⟩, -808550400), (⟨21, by omega⟩, -808550400), (⟨33, by omega⟩, -115507200), (⟨37, by omega⟩, -404275200), (⟨38, by omega⟩, -404275200), (⟨42, by omega⟩, -808550400), (⟨45, by omega⟩, -561563520), (⟨50, by omega⟩, -87619840), (⟨62, by omega⟩, -808550400), (⟨74, by omega⟩, -808550400), (⟨82, by omega⟩, -87619840), (⟨89, by omega⟩, -1123127040)]
  nu := [(⟨0, by omega⟩, -561563520), (⟨3, by omega⟩, 561563520), (⟨4, by omega⟩, 561563520), (⟨5, by omega⟩, -808550400), (⟨10, by omega⟩, -561563520), (⟨12, by omega⟩, 561563520), (⟨16, by omega⟩, -808550400), (⟨20, by omega⟩, -561563520), (⟨21, by omega⟩, 561563520), (⟨22, by omega⟩, 115507200), (⟨23, by omega⟩, 561563520), (⟨25, by omega⟩, -115507200), (⟨26, by omega⟩, -561563520), (⟨28, by omega⟩, -808550400), (⟨30, by omega⟩, -1457733760), (⟨31, by omega⟩, 896170240), (⟨32, by omega⟩, 896170240), (⟨33, by omega⟩, 1370113920), (⟨34, by omega⟩, 649183360), (⟨35, by omega⟩, -808550400), (⟨36, by omega⟩, -808550400), (⟨37, by omega⟩, -87619840), (⟨38, by omega⟩, -808550400), (⟨39, by omega⟩, -87619840), (⟨40, by omega⟩, -561563520)]
  claimed := 1354210245241036144135372800
}
def branch_box_45 : RatBox 8 := { lower := box_45.profileLo, upper := box_45.profileHi }
def accepted_45 : Bool := checkAt 527 1000 box_45 cert_45

def box_47 : Box := { S := 9717120, lo := ![0, 6999363, 0, 6999363, 9383094, 0, 9656388, 0], hi := ![242928, 7166376, 485856, 7166376, 9413460, 121464, 9686754, 242928] }
def cert_47 : Certificate := {
  mu := [(⟨5, by omega⟩, -5734400), (⟨6, by omega⟩, -3982720), (⟨9, by omega⟩, -5734400), (⟨21, by omega⟩, -5734400), (⟨33, by omega⟩, -819200), (⟨37, by omega⟩, -2867200), (⟨38, by omega⟩, -2867200), (⟨42, by omega⟩, -5734400), (⟨45, by omega⟩, -3982720), (⟨50, by omega⟩, -5734400), (⟨62, by omega⟩, -5734400), (⟨74, by omega⟩, -5734400), (⟨82, by omega⟩, -5734400), (⟨89, by omega⟩, -11468800)]
  nu := [(⟨0, by omega⟩, -5734400), (⟨3, by omega⟩, 5734400), (⟨4, by omega⟩, 5734400), (⟨5, by omega⟩, -5734400), (⟨10, by omega⟩, -3982720), (⟨12, by omega⟩, 3982720), (⟨16, by omega⟩, -5734400), (⟨20, by omega⟩, -3982720), (⟨21, by omega⟩, 3982720), (⟨22, by omega⟩, 819200), (⟨23, by omega⟩, 3982720), (⟨25, by omega⟩, -819200), (⟨26, by omega⟩, -3982720), (⟨28, by omega⟩, -5734400), (⟨30, by omega⟩, -17203200), (⟨31, by omega⟩, 11468800), (⟨32, by omega⟩, 11468800), (⟨33, by omega⟩, 11468800), (⟨34, by omega⟩, 11468800), (⟨35, by omega⟩, -5734400), (⟨36, by omega⟩, -5734400), (⟨37, by omega⟩, -5734400), (⟨38, by omega⟩, -5734400), (⟨39, by omega⟩, -5734400), (⟨40, by omega⟩, -5734400)]
  claimed := 483196542329113804800
}
def branch_box_47 : RatBox 8 := { lower := box_47.profileLo, upper := box_47.profileHi }
def accepted_47 : Bool := checkAt 527 1000 box_47 cert_47

end PeaceableQueens.UpperBound.Generated.Even.Core
