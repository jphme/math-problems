import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_2101 : Box := { S := 1909017600, lo := ![0, 1276655520, 0, 1506334200, 1861292160, 23862720, 1861292160, 0], hi := ![47725440, 1309466760, 95450880, 1539145440, 1885154880, 47725440, 1885154880, 23862720] }
def cert_2101 : Certificate := {
  mu := [(⟨4, by omega⟩, -433782120), (⟨5, by omega⟩, -1070284800), (⟨6, by omega⟩, -838732800), (⟨9, by omega⟩, -1070284800), (⟨13, by omega⟩, -115776000), (⟨21, by omega⟩, -115776000), (⟨30, by omega⟩, -115776000), (⟨33, by omega⟩, -94412800), (⟨37, by omega⟩, -1070284800), (⟨42, by omega⟩, -1070284800), (⟨45, by omega⟩, -838732800), (⟨50, by omega⟩, -1070284800), (⟨54, by omega⟩, -838732800), (⟨61, by omega⟩, -94412800), (⟨70, by omega⟩, -137139200), (⟨74, by omega⟩, -1070284800), (⟨77, by omega⟩, -838732800), (⟨82, by omega⟩, -1070284800), (⟨86, by omega⟩, -838732800), (⟨90, by omega⟩, -2140569600), (⟨94, by omega⟩, -1677465600)]
  nu := [(⟨0, by omega⟩, -1070284800), (⟨3, by omega⟩, 1070284800), (⟨4, by omega⟩, 1070284800), (⟨5, by omega⟩, -1070284800), (⟨10, by omega⟩, -838732800), (⟨11, by omega⟩, 115776000), (⟨12, by omega⟩, 838732800), (⟨13, by omega⟩, 838732800), (⟨14, by omega⟩, 838732800), (⟨15, by omega⟩, -115776000), (⟨16, by omega⟩, -115776000), (⟨17, by omega⟩, -115776000), (⟨18, by omega⟩, -838732800), (⟨19, by omega⟩, -838732800), (⟨20, by omega⟩, -838732800), (⟨21, by omega⟩, 838732800), (⟨22, by omega⟩, 94412800), (⟨23, by omega⟩, 838732800), (⟨24, by omega⟩, 838732800), (⟨25, by omega⟩, -94412800), (⟨26, by omega⟩, -838732800), (⟨27, by omega⟩, -838732800), (⟨28, by omega⟩, -94412800), (⟨29, by omega⟩, -137139200), (⟨30, by omega⟩, -3210854400), (⟨31, by omega⟩, 2140569600), (⟨32, by omega⟩, 2140569600), (⟨33, by omega⟩, 2140569600), (⟨34, by omega⟩, 2140569600), (⟨35, by omega⟩, -1070284800), (⟨36, by omega⟩, -1070284800), (⟨37, by omega⟩, -1070284800), (⟨38, by omega⟩, -1070284800), (⟨39, by omega⟩, -1070284800), (⟨40, by omega⟩, -1070284800), (⟨41, by omega⟩, -838732800)]
  claimed := 3631601444240737725972480000
}
def branch_box_2101 : RatBox 8 := { lower := box_2101.profileLo, upper := box_2101.profileHi }
def accepted_2101 : Bool := checkAt 527 1000 box_2101 cert_2101

def box_2106 : Box := { S := 64409600, lo := ![0, 43073920, 0, 51376720, 62799360, 805120, 63604480, 0], hi := ![1610240, 43627440, 3220480, 51930240, 63604480, 1610240, 64409600, 805120] }
def cert_2106 : Certificate := {
  mu := [(⟨5, by omega⟩, -3276800), (⟨6, by omega⟩, -61132800), (⟨9, by omega⟩, -3276800), (⟨13, by omega⟩, -61132800), (⟨21, by omega⟩, -61132800), (⟨34, by omega⟩, -61132800), (⟨37, by omega⟩, -3276800), (⟨42, by omega⟩, -3276800), (⟨45, by omega⟩, -61132800), (⟨50, by omega⟩, -3276800), (⟨61, by omega⟩, -61132800), (⟨74, by omega⟩, -3276800), (⟨77, by omega⟩, -61132800), (⟨82, by omega⟩, -3276800), (⟨89, by omega⟩, -122265600)]
  nu := [(⟨0, by omega⟩, -61132800), (⟨3, by omega⟩, 61132800), (⟨4, by omega⟩, 61132800), (⟨5, by omega⟩, -3276800), (⟨10, by omega⟩, -61132800), (⟨11, by omega⟩, 61132800), (⟨12, by omega⟩, 61132800), (⟨13, by omega⟩, 61132800), (⟨15, by omega⟩, -61132800), (⟨16, by omega⟩, -61132800), (⟨18, by omega⟩, -61132800), (⟨20, by omega⟩, -61132800), (⟨21, by omega⟩, 61132800), (⟨22, by omega⟩, 61132800), (⟨23, by omega⟩, 61132800), (⟨25, by omega⟩, -61132800), (⟨26, by omega⟩, -61132800), (⟨28, by omega⟩, -61132800), (⟨30, by omega⟩, -67686400), (⟨31, by omega⟩, 6553600), (⟨32, by omega⟩, 6553600), (⟨33, by omega⟩, 64409600), (⟨34, by omega⟩, 64409600), (⟨35, by omega⟩, -3276800), (⟨36, by omega⟩, -3276800), (⟨37, by omega⟩, -3276800), (⟨38, by omega⟩, -3276800), (⟨39, by omega⟩, -3276800), (⟨40, by omega⟩, -61132800)]
  claimed := 140808250557275832320000
}
def branch_box_2106 : RatBox 8 := { lower := box_2106.profileLo, upper := box_2106.profileHi }
def accepted_2106 : Bool := checkAt 527 1000 box_2106 cert_2106

def box_2108 : Box := { S := 6400, lo := ![0, 4335, 0, 5105, 6240, 80, 6320, 0], hi := ![160, 4390, 320, 5160, 6320, 160, 6400, 80] }
def cert_2108 : Certificate := {
  mu := [(⟨6, by omega⟩, -6400), (⟨45, by omega⟩, -6400), (⟨77, by omega⟩, -6400), (⟨89, by omega⟩, -12800)]
  nu := [(⟨0, by omega⟩, -6400), (⟨3, by omega⟩, 6400), (⟨4, by omega⟩, 6400), (⟨10, by omega⟩, -6400), (⟨12, by omega⟩, 6400), (⟨13, by omega⟩, 6400), (⟨18, by omega⟩, -6400), (⟨20, by omega⟩, -6400), (⟨21, by omega⟩, 6400), (⟨23, by omega⟩, 6400), (⟨26, by omega⟩, -6400), (⟨30, by omega⟩, -6400), (⟨33, by omega⟩, 6400), (⟨34, by omega⟩, 6400), (⟨40, by omega⟩, -6400)]
  claimed := 136069120000
}
def branch_box_2108 : RatBox 8 := { lower := box_2108.profileLo, upper := box_2108.profileHi }
def accepted_2108 : Bool := checkAt 527 1000 box_2108 cert_2108

def box_2110 : Box := { S := 73757122560, lo := ![0, 50275851120, 0, 58198979520, 71913194496, 921964032, 72835158528, 0], hi := ![1843928064, 50592776256, 3687856128, 58832829792, 72835158528, 1843928064, 73757122560, 921964032] }
def cert_2110 : Certificate := {
  mu := [(⟨5, by omega⟩, -3719823360), (⟨6, by omega⟩, -70037299200), (⟨10, by omega⟩, -3719823360), (⟨13, by omega⟩, -3384279040), (⟨21, by omega⟩, -3384279040), (⟨38, by omega⟩, -3719823360), (⟨42, by omega⟩, -3719823360), (⟨45, by omega⟩, -70037299200), (⟨50, by omega⟩, -3719823360), (⟨54, by omega⟩, -335544320), (⟨69, by omega⟩, -3384279040), (⟨74, by omega⟩, -3719823360), (⟨77, by omega⟩, -70037299200), (⟨82, by omega⟩, -3719823360), (⟨86, by omega⟩, -335544320), (⟨89, by omega⟩, -140074598400), (⟨94, by omega⟩, -671088640)]
  nu := [(⟨0, by omega⟩, -70037299200), (⟨3, by omega⟩, 70037299200), (⟨4, by omega⟩, 70037299200), (⟨5, by omega⟩, -3719823360), (⟨10, by omega⟩, -70037299200), (⟨11, by omega⟩, 3384279040), (⟨12, by omega⟩, 70037299200), (⟨13, by omega⟩, 70037299200), (⟨14, by omega⟩, 335544320), (⟨15, by omega⟩, -3384279040), (⟨16, by omega⟩, -3384279040), (⟨18, by omega⟩, -70037299200), (⟨19, by omega⟩, -335544320), (⟨20, by omega⟩, -70037299200), (⟨21, by omega⟩, 70037299200), (⟨23, by omega⟩, 70037299200), (⟨24, by omega⟩, 335544320), (⟨26, by omega⟩, -70037299200), (⟨27, by omega⟩, -335544320), (⟨29, by omega⟩, -3384279040), (⟨30, by omega⟩, -77476945920), (⟨31, by omega⟩, 7439646720), (⟨32, by omega⟩, 7439646720), (⟨33, by omega⟩, 73757122560), (⟨34, by omega⟩, 73757122560), (⟨35, by omega⟩, -3719823360), (⟨36, by omega⟩, -3719823360), (⟨37, by omega⟩, -3719823360), (⟨38, by omega⟩, -3719823360), (⟨39, by omega⟩, -3719823360), (⟨40, by omega⟩, -70037299200), (⟨41, by omega⟩, -335544320)]
  claimed := 209912143364649349788698306150400
}
def branch_box_2110 : RatBox 8 := { lower := box_2110.profileLo, upper := box_2110.profileHi }
def accepted_2110 : Bool := checkAt 527 1000 box_2110 cert_2110

def box_2112 : Box := { S := 8089600, lo := ![0, 5479440, 0, 6383200, 7988480, 101120, 7887360, 0], hi := ![202240, 5548960, 404480, 6522240, 8089600, 202240, 8089600, 101120] }
def cert_2112 : Certificate := {
  mu := [(⟨4, by omega⟩, -306520), (⟨6, by omega⟩, -8089600), (⟨34, by omega⟩, -8089600), (⟨45, by omega⟩, -8089600), (⟨54, by omega⟩, -8089600), (⟨61, by omega⟩, -8089600), (⟨70, by omega⟩, -8089600), (⟨77, by omega⟩, -8089600), (⟨86, by omega⟩, -8089600), (⟨90, by omega⟩, -16073600), (⟨94, by omega⟩, -320803200)]
  nu := [(⟨0, by omega⟩, -8089600), (⟨3, by omega⟩, 8036800), (⟨4, by omega⟩, 8089600), (⟨10, by omega⟩, -8089600), (⟨12, by omega⟩, 8089600), (⟨13, by omega⟩, 8089600), (⟨14, by omega⟩, 8089600), (⟨18, by omega⟩, -8089600), (⟨19, by omega⟩, -8089600), (⟨20, by omega⟩, -8089600), (⟨21, by omega⟩, 8089600), (⟨22, by omega⟩, 8089600), (⟨23, by omega⟩, 8089600), (⟨24, by omega⟩, 8089600), (⟨25, by omega⟩, -8089600), (⟨26, by omega⟩, -8089600), (⟨27, by omega⟩, -8089600), (⟨28, by omega⟩, -8089600), (⟨29, by omega⟩, -8089600), (⟨30, by omega⟩, -8089600), (⟨33, by omega⟩, 8036800), (⟨34, by omega⟩, 8089600), (⟨40, by omega⟩, -8036800), (⟨41, by omega⟩, -8089600)]
  claimed := 278951680519700480000
}
def branch_box_2112 : RatBox 8 := { lower := box_2112.profileLo, upper := box_2112.profileHi }
def accepted_2112 : Bool := checkAt 527 1000 box_2112 cert_2112

def box_2114 : Box := { S := 8089600, lo := ![0, 5409920, 0, 6452720, 7988480, 101120, 7887360, 0], hi := ![202240, 5479440, 404480, 6522240, 8089600, 202240, 8089600, 101120] }
def cert_2114 : Certificate := {
  mu := [(⟨4, by omega⟩, -271760), (⟨6, by omega⟩, -8089600), (⟨34, by omega⟩, -8089600), (⟨45, by omega⟩, -8089600), (⟨54, by omega⟩, -8089600), (⟨61, by omega⟩, -8089600), (⟨70, by omega⟩, -8089600), (⟨77, by omega⟩, -8089600), (⟨86, by omega⟩, -8089600), (⟨90, by omega⟩, -16108800), (⟨94, by omega⟩, -323584000)]
  nu := [(⟨0, by omega⟩, -8089600), (⟨3, by omega⟩, 8054400), (⟨4, by omega⟩, 8089600), (⟨10, by omega⟩, -8089600), (⟨12, by omega⟩, 8089600), (⟨13, by omega⟩, 8089600), (⟨14, by omega⟩, 8089600), (⟨18, by omega⟩, -8089600), (⟨19, by omega⟩, -8089600), (⟨20, by omega⟩, -8089600), (⟨21, by omega⟩, 8089600), (⟨22, by omega⟩, 8089600), (⟨23, by omega⟩, 8089600), (⟨24, by omega⟩, 8089600), (⟨25, by omega⟩, -8089600), (⟨26, by omega⟩, -8089600), (⟨27, by omega⟩, -8089600), (⟨28, by omega⟩, -8089600), (⟨29, by omega⟩, -8089600), (⟨30, by omega⟩, -8089600), (⟨33, by omega⟩, 8054400), (⟨34, by omega⟩, 8089600), (⟨40, by omega⟩, -8054400), (⟨41, by omega⟩, -8089600)]
  claimed := 278951680519700480000
}
def branch_box_2114 : RatBox 8 := { lower := box_2114.profileLo, upper := box_2114.profileHi }
def accepted_2114 : Bool := checkAt 527 1000 box_2114 cert_2114

def box_2115 : Box := { S := 1690087756800, lo := ![0, 1130246187360, 0, 1333584870600, 1647835562880, 21126096960, 1647835562880, 21126096960], hi := ![42252193920, 1159294570680, 84504387840, 1362633253920, 1668961659840, 42252193920, 1690087756800, 42252193920] }
def cert_2115 : Certificate := {
  mu := [(⟨5, by omega⟩, -940780339200), (⟨6, by omega⟩, -749307417600), (⟨9, by omega⟩, -940780339200), (⟨13, by omega⟩, -95736460800), (⟨21, by omega⟩, -95736460800), (⟨29, by omega⟩, -95736460800), (⟨33, by omega⟩, -82508800000), (⟨37, by omega⟩, -940780339200), (⟨42, by omega⟩, -940780339200), (⟨45, by omega⟩, -749307417600), (⟨50, by omega⟩, -81835622400), (⟨53, by omega⟩, -749307417600), (⟨61, by omega⟩, -108964121600), (⟨69, by omega⟩, -82508800000), (⟨74, by omega⟩, -940780339200), (⟨77, by omega⟩, -749307417600), (⟨82, by omega⟩, -81835622400), (⟨85, by omega⟩, -749307417600), (⟨90, by omega⟩, -1498614835200), (⟨93, by omega⟩, -1498614835200)]
  nu := [(⟨0, by omega⟩, -749307417600), (⟨3, by omega⟩, 749307417600), (⟨4, by omega⟩, 749307417600), (⟨5, by omega⟩, -940780339200), (⟨10, by omega⟩, -749307417600), (⟨11, by omega⟩, 95736460800), (⟨12, by omega⟩, 749307417600), (⟨13, by omega⟩, 749307417600), (⟨14, by omega⟩, 749307417600), (⟨15, by omega⟩, -95736460800), (⟨16, by omega⟩, -95736460800), (⟨17, by omega⟩, -95736460800), (⟨18, by omega⟩, -749307417600), (⟨19, by omega⟩, -749307417600), (⟨20, by omega⟩, -749307417600), (⟨21, by omega⟩, 749307417600), (⟨22, by omega⟩, 82508800000), (⟨23, by omega⟩, 749307417600), (⟨24, by omega⟩, 749307417600), (⟨25, by omega⟩, -82508800000), (⟨26, by omega⟩, -749307417600), (⟨27, by omega⟩, -749307417600), (⟨28, by omega⟩, -108964121600), (⟨29, by omega⟩, -82508800000), (⟨30, by omega⟩, -1771923379200), (⟨31, by omega⟩, 1022615961600), (⟨32, by omega⟩, 1022615961600), (⟨33, by omega⟩, 1690087756800), (⟨34, by omega⟩, 831143040000), (⟨35, by omega⟩, -940780339200), (⟨36, by omega⟩, -940780339200), (⟨37, by omega⟩, -81835622400), (⟨38, by omega⟩, -940780339200), (⟨39, by omega⟩, -81835622400), (⟨40, by omega⟩, -749307417600), (⟨41, by omega⟩, -749307417600)]
  claimed := 2534752287748075795502237926686720000
}
def branch_box_2115 : RatBox 8 := { lower := box_2115.profileLo, upper := box_2115.profileHi }
def accepted_2115 : Bool := checkAt 527 1000 box_2115 cert_2115

def box_2118 : Box := { S := 51200, lo := ![0, 34680, 0, 40400, 50560, 640, 49920, 640], hi := ![1280, 35120, 2560, 41280, 51200, 1280, 51200, 1280] }
def cert_2118 : Certificate := {
  mu := [(⟨4, by omega⟩, -1280), (⟨6, by omega⟩, -51200), (⟨13, by omega⟩, -51200), (⟨21, by omega⟩, -51200), (⟨29, by omega⟩, -51200), (⟨45, by omega⟩, -51200), (⟨53, by omega⟩, -51200), (⟨77, by omega⟩, -51200), (⟨85, by omega⟩, -51200), (⟨90, by omega⟩, -102400), (⟨93, by omega⟩, -102400)]
  nu := [(⟨0, by omega⟩, -51200), (⟨3, by omega⟩, 51200), (⟨4, by omega⟩, 51200), (⟨10, by omega⟩, -51200), (⟨11, by omega⟩, 51200), (⟨12, by omega⟩, 51200), (⟨13, by omega⟩, 51200), (⟨14, by omega⟩, 51200), (⟨15, by omega⟩, -51200), (⟨16, by omega⟩, -51200), (⟨17, by omega⟩, -51200), (⟨18, by omega⟩, -51200), (⟨19, by omega⟩, -51200), (⟨20, by omega⟩, -51200), (⟨21, by omega⟩, 51200), (⟨23, by omega⟩, 51200), (⟨24, by omega⟩, 51200), (⟨26, by omega⟩, -51200), (⟨27, by omega⟩, -51200), (⟨30, by omega⟩, -51200), (⟨33, by omega⟩, 51200), (⟨34, by omega⟩, 51200), (⟨40, by omega⟩, -51200), (⟨41, by omega⟩, -51200)]
  claimed := 69911183360000
}
def branch_box_2118 : RatBox 8 := { lower := box_2118.profileLo, upper := box_2118.profileHi }
def accepted_2118 : Bool := checkAt 527 1000 box_2118 cert_2118

def box_2120 : Box := { S := 51200, lo := ![0, 34240, 0, 40840, 50560, 640, 49920, 640], hi := ![1280, 34680, 2560, 41280, 51200, 1280, 51200, 1280] }
def cert_2120 : Certificate := {
  mu := [(⟨4, by omega⟩, -1280), (⟨6, by omega⟩, -51200), (⟨45, by omega⟩, -51200), (⟨53, by omega⟩, -51200), (⟨77, by omega⟩, -51200), (⟨85, by omega⟩, -51200), (⟨90, by omega⟩, -102400), (⟨93, by omega⟩, -102400)]
  nu := [(⟨0, by omega⟩, -51200), (⟨3, by omega⟩, 51200), (⟨4, by omega⟩, 51200), (⟨10, by omega⟩, -51200), (⟨12, by omega⟩, 51200), (⟨13, by omega⟩, 51200), (⟨14, by omega⟩, 51200), (⟨18, by omega⟩, -51200), (⟨19, by omega⟩, -51200), (⟨20, by omega⟩, -51200), (⟨21, by omega⟩, 51200), (⟨23, by omega⟩, 51200), (⟨24, by omega⟩, 51200), (⟨26, by omega⟩, -51200), (⟨27, by omega⟩, -51200), (⟨30, by omega⟩, -51200), (⟨33, by omega⟩, 51200), (⟨34, by omega⟩, 51200), (⟨40, by omega⟩, -51200), (⟨41, by omega⟩, -51200)]
  claimed := 69911183360000
}
def branch_box_2120 : RatBox 8 := { lower := box_2120.profileLo, upper := box_2120.profileHi }
def accepted_2120 : Bool := checkAt 527 1000 box_2120 cert_2120

def box_2122 : Box := { S := 11467653120, lo := ![0, 7668993024, 0, 9048695040, 11324307456, 215018496, 11180961792, 143345664], hi := ![286691328, 7767543168, 573382656, 9147245184, 11467653120, 286691328, 11467653120, 286691328] }
def cert_2122 : Certificate := {
  mu := [(⟨4, by omega⟩, -2752859232), (⟨5, by omega⟩, -6013071360), (⟨6, by omega⟩, -5454581760), (⟨9, by omega⟩, -6013071360), (⟨13, by omega⟩, -279244800), (⟨21, by omega⟩, -279244800), (⟨30, by omega⟩, -279244800), (⟨34, by omega⟩, -534495232), (⟨37, by omega⟩, -6013071360), (⟨42, by omega⟩, -6013071360), (⟨46, by omega⟩, -5454581760), (⟨54, by omega⟩, -5454581760), (⟨62, by omega⟩, -534495232), (⟨70, by omega⟩, -534495232), (⟨74, by omega⟩, -6013071360), (⟨77, by omega⟩, -5454581760), (⟨79, by omega⟩, -3315953664), (⟨86, by omega⟩, -5454581760), (⟨90, by omega⟩, -10909163520), (⟨94, by omega⟩, -10909163520)]
  nu := [(⟨0, by omega⟩, -5454581760), (⟨3, by omega⟩, 5454581760), (⟨4, by omega⟩, 5454581760), (⟨5, by omega⟩, -6013071360), (⟨10, by omega⟩, -5454581760), (⟨11, by omega⟩, 279244800), (⟨12, by omega⟩, 5454581760), (⟨13, by omega⟩, 5454581760), (⟨14, by omega⟩, 5454581760), (⟨15, by omega⟩, -279244800), (⟨16, by omega⟩, -279244800), (⟨17, by omega⟩, -279244800), (⟨18, by omega⟩, -5454581760), (⟨19, by omega⟩, -5454581760), (⟨20, by omega⟩, -5454581760), (⟨21, by omega⟩, 5454581760), (⟨22, by omega⟩, 534495232), (⟨23, by omega⟩, 5454581760), (⟨24, by omega⟩, 5454581760), (⟨25, by omega⟩, -534495232), (⟨26, by omega⟩, -5454581760), (⟨27, by omega⟩, -5454581760), (⟨28, by omega⟩, -534495232), (⟨29, by omega⟩, -534495232), (⟨30, by omega⟩, -11467653120), (⟨31, by omega⟩, 6013071360), (⟨32, by omega⟩, 2697117696), (⟨33, by omega⟩, 11467653120), (⟨34, by omega⟩, 5454581760), (⟨35, by omega⟩, -6013071360), (⟨36, by omega⟩, -6013071360), (⟨38, by omega⟩, -6013071360), (⟨39, by omega⟩, 3315953664), (⟨40, by omega⟩, -5454581760), (⟨41, by omega⟩, -5454581760)]
  claimed := 792113022643979201765651251200
}
def branch_box_2122 : RatBox 8 := { lower := box_2122.profileLo, upper := box_2122.profileHi }
def accepted_2122 : Bool := checkAt 527 1000 box_2122 cert_2122

def box_2124 : Box := { S := 329318400, lo := ![0, 225891840, 0, 259852800, 321085440, 0, 321085440, 0], hi := ![8232960, 231552000, 16465920, 265512960, 329318400, 8232960, 329318400, 8232960] }
def cert_2124 : Certificate := {
  mu := [(⟨5, by omega⟩, -16465920), (⟨6, by omega⟩, -312852480), (⟨9, by omega⟩, -16465920), (⟨21, by omega⟩, -16465920), (⟨34, by omega⟩, -1310720), (⟨37, by omega⟩, -16465920), (⟨42, by omega⟩, -16465920), (⟨46, by omega⟩, -328007680), (⟨50, by omega⟩, -16465920), (⟨61, by omega⟩, -1310720), (⟨74, by omega⟩, -16465920), (⟨82, by omega⟩, -16465920), (⟨89, by omega⟩, -312852480), (⟨90, by omega⟩, -312852480)]
  nu := [(⟨0, by omega⟩, -312852480), (⟨3, by omega⟩, 312852480), (⟨4, by omega⟩, 312852480), (⟨5, by omega⟩, -16465920), (⟨10, by omega⟩, -312852480), (⟨12, by omega⟩, 312852480), (⟨16, by omega⟩, -16465920), (⟨20, by omega⟩, -312852480), (⟨21, by omega⟩, 312852480), (⟨22, by omega⟩, 1310720), (⟨23, by omega⟩, 312852480), (⟨25, by omega⟩, -1310720), (⟨26, by omega⟩, -328007680), (⟨28, by omega⟩, -1310720), (⟨30, by omega⟩, -345784320), (⟨31, by omega⟩, 32931840), (⟨32, by omega⟩, 32931840), (⟨33, by omega⟩, 329318400), (⟨34, by omega⟩, 329318400), (⟨35, by omega⟩, -16465920), (⟨36, by omega⟩, -16465920), (⟨37, by omega⟩, -16465920), (⟨38, by omega⟩, -16465920), (⟨39, by omega⟩, -16465920), (⟨40, by omega⟩, -312852480)]
  claimed := 18779273870225398824960000
}
def branch_box_2124 : RatBox 8 := { lower := box_2124.profileLo, upper := box_2124.profileHi }
def accepted_2124 : Bool := checkAt 527 1000 box_2124 cert_2124

def box_2135 : Box := { S := 1065521920, lo := ![0, 730881442, 0, 822449732, 1038883872, 0, 1038883872, 0], hi := ![26638048, 740038271, 53276096, 831606561, 1045543384, 13319024, 1052202896, 26638048] }
def cert_2135 : Certificate := {
  mu := [(⟨5, by omega⟩, -640614400), (⟨6, by omega⟩, -424907520), (⟨9, by omega⟩, -640614400), (⟨21, by omega⟩, -640614400), (⟨33, by omega⟩, -78643200), (⟨37, by omega⟩, -640614400), (⟨41, by omega⟩, -640614400), (⟨45, by omega⟩, -52428800), (⟨49, by omega⟩, -640614400), (⟨62, by omega⟩, -640614400), (⟨74, by omega⟩, -640614400), (⟨82, by omega⟩, -640614400), (⟨89, by omega⟩, -1281228800)]
  nu := [(⟨0, by omega⟩, -640614400), (⟨3, by omega⟩, 640614400), (⟨4, by omega⟩, 640614400), (⟨5, by omega⟩, -640614400), (⟨10, by omega⟩, -424907520), (⟨12, by omega⟩, 424907520), (⟨16, by omega⟩, -640614400), (⟨20, by omega⟩, -424907520), (⟨21, by omega⟩, 424907520), (⟨22, by omega⟩, 78643200), (⟨23, by omega⟩, 52428800), (⟨25, by omega⟩, -78643200), (⟨26, by omega⟩, -52428800), (⟨28, by omega⟩, -640614400), (⟨30, by omega⟩, -1921843200), (⟨31, by omega⟩, 1281228800), (⟨32, by omega⟩, 1281228800), (⟨33, by omega⟩, 1281228800), (⟨34, by omega⟩, 1281228800), (⟨35, by omega⟩, -640614400), (⟨36, by omega⟩, -640614400), (⟨37, by omega⟩, -640614400), (⟨38, by omega⟩, -640614400), (⟨39, by omega⟩, -640614400), (⟨40, by omega⟩, -640614400)]
  claimed := 637059160081479282289868800
}
def branch_box_2135 : RatBox 8 := { lower := box_2135.profileLo, upper := box_2135.profileHi }
def accepted_2135 : Bool := checkAt 527 1000 box_2135 cert_2135

def box_2137 : Box := { S := 13625600, lo := ![0, 9346310, 0, 10517260, 13370120, 0, 13284960, 0], hi := ![340640, 9463405, 681280, 10634355, 13455280, 170320, 13370120, 340640] }
def cert_2137 : Certificate := {
  mu := [(⟨4, by omega⟩, -2852640), (⟨5, by omega⟩, -8192000), (⟨6, by omega⟩, -5433600), (⟨9, by omega⟩, -8192000), (⟨21, by omega⟩, -2758400), (⟨33, by omega⟩, -1379200), (⟨37, by omega⟩, -8192000), (⟨41, by omega⟩, -8192000), (⟨45, by omega⟩, -5433600), (⟨50, by omega⟩, -8192000), (⟨53, by omega⟩, -5433600), (⟨62, by omega⟩, -1379200), (⟨70, by omega⟩, -1379200), (⟨74, by omega⟩, -8192000), (⟨82, by omega⟩, -8192000), (⟨85, by omega⟩, -5433600), (⟨89, by omega⟩, -16384000), (⟨94, by omega⟩, -10867200)]
  nu := [(⟨0, by omega⟩, -8192000), (⟨3, by omega⟩, 8192000), (⟨4, by omega⟩, 8192000), (⟨5, by omega⟩, -8192000), (⟨10, by omega⟩, -5433600), (⟨12, by omega⟩, 5433600), (⟨14, by omega⟩, 5433600), (⟨16, by omega⟩, -2758400), (⟨19, by omega⟩, -5433600), (⟨20, by omega⟩, -5433600), (⟨21, by omega⟩, 5433600), (⟨22, by omega⟩, 1379200), (⟨23, by omega⟩, 5433600), (⟨24, by omega⟩, 5433600), (⟨25, by omega⟩, -1379200), (⟨26, by omega⟩, -5433600), (⟨27, by omega⟩, -5433600), (⟨28, by omega⟩, -1379200), (⟨29, by omega⟩, -1379200), (⟨30, by omega⟩, -24576000), (⟨31, by omega⟩, 16384000), (⟨32, by omega⟩, 16384000), (⟨33, by omega⟩, 16384000), (⟨34, by omega⟩, 16384000), (⟨35, by omega⟩, -8192000), (⟨36, by omega⟩, -8192000), (⟨37, by omega⟩, -8192000), (⟨38, by omega⟩, -8192000), (⟨39, by omega⟩, -8192000), (⟨40, by omega⟩, -8192000), (⟨41, by omega⟩, -5433600)]
  claimed := 1328859480778588160000
}
def branch_box_2137 : RatBox 8 := { lower := box_2137.profileLo, upper := box_2137.profileHi }
def accepted_2137 : Bool := checkAt 527 1000 box_2137 cert_2137

def box_2139 : Box := { S := 2865920, lo := ![0, 1965842, 0, 2236761, 2794272, 0, 2794272, 0], hi := ![71648, 1990471, 143296, 2261390, 2812184, 35824, 2830096, 71648] }
def cert_2139 : Certificate := {
  mu := [(⟨5, by omega⟩, -1638400), (⟨6, by omega⟩, -1227520), (⟨9, by omega⟩, -1638400), (⟨21, by omega⟩, -1638400), (⟨33, by omega⟩, -1227520), (⟨37, by omega⟩, -1638400), (⟨42, by omega⟩, -1638400), (⟨45, by omega⟩, -1227520), (⟨50, by omega⟩, -1638400), (⟨62, by omega⟩, -1638400), (⟨74, by omega⟩, -1638400), (⟨82, by omega⟩, -1638400), (⟨89, by omega⟩, -3276800)]
  nu := [(⟨0, by omega⟩, -1638400), (⟨3, by omega⟩, 1638400), (⟨4, by omega⟩, 1638400), (⟨5, by omega⟩, -1638400), (⟨10, by omega⟩, -1227520), (⟨12, by omega⟩, 1227520), (⟨16, by omega⟩, -1638400), (⟨20, by omega⟩, -1227520), (⟨21, by omega⟩, 1227520), (⟨22, by omega⟩, 1227520), (⟨23, by omega⟩, 1227520), (⟨25, by omega⟩, -1227520), (⟨26, by omega⟩, -1227520), (⟨28, by omega⟩, -1638400), (⟨30, by omega⟩, -4915200), (⟨31, by omega⟩, 3276800), (⟨32, by omega⟩, 3276800), (⟨33, by omega⟩, 3276800), (⟨34, by omega⟩, 3276800), (⟨35, by omega⟩, -1638400), (⟨36, by omega⟩, -1638400), (⟨37, by omega⟩, -1638400), (⟨38, by omega⟩, -1638400), (⟨39, by omega⟩, -1638400), (⟨40, by omega⟩, -1638400)]
  claimed := 12394225141099724800
}
def branch_box_2139 : RatBox 8 := { lower := box_2139.profileLo, upper := box_2139.profileHi }
def accepted_2139 : Bool := checkAt 527 1000 box_2139 cert_2139

def box_2141 : Box := { S := 558854400, lo := ![0, 383339190, 0, 436168395, 548375880, 0, 544883040, 0], hi := ![13971360, 388141845, 27942720, 440971050, 551868720, 6985680, 548375880, 13971360] }
def cert_2141 : Certificate := {
  mu := [(⟨4, by omega⟩, -125667360), (⟨5, by omega⟩, -319488000), (⟨6, by omega⟩, -239366400), (⟨9, by omega⟩, -319488000), (⟨21, by omega⟩, -80121600), (⟨33, by omega⟩, -239366400), (⟨37, by omega⟩, -319488000), (⟨42, by omega⟩, -319488000), (⟨45, by omega⟩, -239366400), (⟨50, by omega⟩, -319488000), (⟨53, by omega⟩, -239366400), (⟨62, by omega⟩, -239366400), (⟨70, by omega⟩, -239366400), (⟨74, by omega⟩, -319488000), (⟨82, by omega⟩, -319488000), (⟨86, by omega⟩, -239366400), (⟨89, by omega⟩, -631417600), (⟨94, by omega⟩, -478732800)]
  nu := [(⟨0, by omega⟩, -319488000), (⟨3, by omega⟩, 319488000), (⟨4, by omega⟩, 319488000), (⟨5, by omega⟩, -319488000), (⟨10, by omega⟩, -239366400), (⟨12, by omega⟩, 239366400), (⟨14, by omega⟩, 239366400), (⟨16, by omega⟩, -80121600), (⟨19, by omega⟩, -239366400), (⟨20, by omega⟩, -239366400), (⟨21, by omega⟩, 239366400), (⟨22, by omega⟩, 239366400), (⟨23, by omega⟩, 239366400), (⟨24, by omega⟩, 239366400), (⟨25, by omega⟩, -239366400), (⟨26, by omega⟩, -239366400), (⟨27, by omega⟩, -239366400), (⟨28, by omega⟩, -239366400), (⟨29, by omega⟩, -239366400), (⟨30, by omega⟩, -958464000), (⟨31, by omega⟩, 638976000), (⟨32, by omega⟩, 638976000), (⟨33, by omega⟩, 638976000), (⟨34, by omega⟩, 638976000), (⟨35, by omega⟩, -319488000), (⟨36, by omega⟩, -319488000), (⟨37, by omega⟩, -319488000), (⟨38, by omega⟩, -319488000), (⟨39, by omega⟩, -319488000), (⟨40, by omega⟩, -319488000), (⟨41, by omega⟩, -239366400)]
  claimed := 91656328838419116195840000
}
def branch_box_2141 : RatBox 8 := { lower := box_2141.profileLo, upper := box_2141.profileHi }
def accepted_2141 : Bool := checkAt 527 1000 box_2141 cert_2141

def box_2146 : Box := { S := 530841600, lo := ![0, 366405120, 0, 416586240, 520888320, 0, 520888320, 0], hi := ![13271040, 368686080, 26542080, 418867200, 524206080, 6635520, 524206080, 13271040] }
def cert_2146 : Certificate := {
  mu := [(⟨5, by omega⟩, -32768000), (⟨6, by omega⟩, -498073600), (⟨9, by omega⟩, -32768000), (⟨21, by omega⟩, -32768000), (⟨34, by omega⟩, -498073600), (⟨38, by omega⟩, -32768000), (⟨42, by omega⟩, -32768000), (⟨46, by omega⟩, -498073600), (⟨50, by omega⟩, -32768000), (⟨62, by omega⟩, -498073600), (⟨74, by omega⟩, -32768000), (⟨82, by omega⟩, -32768000), (⟨89, by omega⟩, -498073600), (⟨90, by omega⟩, -498073600)]
  nu := [(⟨0, by omega⟩, -498073600), (⟨3, by omega⟩, 498073600), (⟨4, by omega⟩, 498073600), (⟨5, by omega⟩, -32768000), (⟨10, by omega⟩, -498073600), (⟨12, by omega⟩, 498073600), (⟨16, by omega⟩, -32768000), (⟨20, by omega⟩, -498073600), (⟨21, by omega⟩, 498073600), (⟨22, by omega⟩, 498073600), (⟨23, by omega⟩, 498073600), (⟨25, by omega⟩, -498073600), (⟨26, by omega⟩, -498073600), (⟨28, by omega⟩, -498073600), (⟨30, by omega⟩, -563609600), (⟨31, by omega⟩, 65536000), (⟨32, by omega⟩, 65536000), (⟨33, by omega⟩, 530841600), (⟨34, by omega⟩, 530841600), (⟨35, by omega⟩, -32768000), (⟨36, by omega⟩, -32768000), (⟨37, by omega⟩, -32768000), (⟨38, by omega⟩, -32768000), (⟨39, by omega⟩, -32768000), (⟨40, by omega⟩, -498073600)]
  claimed := 78621512032768732692480000
}
def branch_box_2146 : RatBox 8 := { lower := box_2146.profileLo, upper := box_2146.profileHi }
def accepted_2146 : Bool := checkAt 527 1000 box_2146 cert_2146

def box_2148 : Box := { S := 18876006400, lo := ![0, 13109976320, 0, 14732133120, 18404106240, 0, 18404106240, 0], hi := ![471900160, 13272192000, 943800320, 14894348800, 18640056320, 235950080, 18640056320, 471900160] }
def cert_2148 : Certificate := {
  mu := [(⟨5, by omega⟩, -1381171200), (⟨6, by omega⟩, -17494835200), (⟨9, by omega⟩, -1381171200), (⟨21, by omega⟩, -1381171200), (⟨34, by omega⟩, -18876006400), (⟨37, by omega⟩, -1381171200), (⟨42, by omega⟩, -1381171200), (⟨50, by omega⟩, -1381171200), (⟨74, by omega⟩, -1381171200), (⟨78, by omega⟩, -157286400), (⟨82, by omega⟩, -1381171200), (⟨89, by omega⟩, -17494835200), (⟨90, by omega⟩, -17494835200)]
  nu := [(⟨0, by omega⟩, -17494835200), (⟨3, by omega⟩, 17494835200), (⟨4, by omega⟩, 17494835200), (⟨5, by omega⟩, -1381171200), (⟨10, by omega⟩, -17494835200), (⟨12, by omega⟩, 17494835200), (⟨13, by omega⟩, 157286400), (⟨16, by omega⟩, -1381171200), (⟨18, by omega⟩, -157286400), (⟨20, by omega⟩, -17494835200), (⟨21, by omega⟩, 17494835200), (⟨22, by omega⟩, 17494835200), (⟨25, by omega⟩, -18876006400), (⟨30, by omega⟩, -20257177600), (⟨31, by omega⟩, 2762342400), (⟨32, by omega⟩, 2762342400), (⟨33, by omega⟩, 18876006400), (⟨34, by omega⟩, 18876006400), (⟨35, by omega⟩, -1381171200), (⟨36, by omega⟩, -1381171200), (⟨37, by omega⟩, -1381171200), (⟨38, by omega⟩, -1381171200), (⟨39, by omega⟩, -1381171200), (⟨40, by omega⟩, -17494835200)]
  claimed := 3535433969448685779298549760000
}
def branch_box_2148 : RatBox 8 := { lower := box_2148.profileLo, upper := box_2148.profileHi }
def accepted_2148 : Bool := checkAt 527 1000 box_2148 cert_2148

def box_2149 : Box := { S := 712960, lo := ![0, 495173, 0, 550316, 695136, 0, 695136, 0], hi := ![17824, 501300, 35648, 556443, 699592, 8912, 704048, 17824] }
def cert_2149 : Certificate := {
  mu := [(⟨5, by omega⟩, -409600), (⟨6, by omega⟩, -303360), (⟨9, by omega⟩, -409600), (⟨21, by omega⟩, -409600), (⟨33, by omega⟩, -303360), (⟨37, by omega⟩, -409600), (⟨42, by omega⟩, -409600), (⟨45, by omega⟩, -303360), (⟨50, by omega⟩, -409600), (⟨62, by omega⟩, -409600), (⟨74, by omega⟩, -409600), (⟨82, by omega⟩, -409600), (⟨89, by omega⟩, -819200)]
  nu := [(⟨0, by omega⟩, -409600), (⟨3, by omega⟩, 409600), (⟨4, by omega⟩, 409600), (⟨5, by omega⟩, -409600), (⟨10, by omega⟩, -303360), (⟨12, by omega⟩, 303360), (⟨16, by omega⟩, -409600), (⟨20, by omega⟩, -303360), (⟨21, by omega⟩, 303360), (⟨22, by omega⟩, 303360), (⟨23, by omega⟩, 303360), (⟨25, by omega⟩, -303360), (⟨26, by omega⟩, -303360), (⟨28, by omega⟩, -409600), (⟨30, by omega⟩, -1228800), (⟨31, by omega⟩, 819200), (⟨32, by omega⟩, 819200), (⟨33, by omega⟩, 819200), (⟨34, by omega⟩, 819200), (⟨35, by omega⟩, -409600), (⟨36, by omega⟩, -409600), (⟨37, by omega⟩, -409600), (⟨38, by omega⟩, -409600), (⟨39, by omega⟩, -409600), (⟨40, by omega⟩, -409600)]
  claimed := 190960604486041600
}
def branch_box_2149 : RatBox 8 := { lower := box_2149.profileLo, upper := box_2149.profileHi }
def accepted_2149 : Bool := checkAt 527 1000 box_2149 cert_2149

end PeaceableQueens.UpperBound.Generated.Even.Core
