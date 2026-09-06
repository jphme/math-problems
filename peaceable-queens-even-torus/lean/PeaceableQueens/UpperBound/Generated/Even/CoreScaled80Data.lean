import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_4004 : Box := { S := 615383040, lo := ![0, 459133440, 0, 443268096, 599998464, 0, 599998464, 0], hi := ![15384576, 464421888, 30769152, 453844992, 607690752, 7692288, 607690752, 15384576] }
def cert_4004 : Certificate := {
  mu := [(⟨3, by omega⟩, -76793600), (⟨4, by omega⟩, -7823360), (⟨5, by omega⟩, -312934400), (⟨6, by omega⟩, -302448640), (⟨10, by omega⟩, -312934400), (⟨21, by omega⟩, -312934400), (⟨34, by omega⟩, -302448640), (⟨38, by omega⟩, -312934400), (⟨42, by omega⟩, -312934400), (⟨50, by omega⟩, -312934400), (⟨69, by omega⟩, -312934400), (⟨74, by omega⟩, -312934400), (⟨82, by omega⟩, -312934400), (⟨85, by omega⟩, -302448640), (⟨89, by omega⟩, -625868800)]
  nu := [(⟨0, by omega⟩, -312934400), (⟨3, by omega⟩, 312934400), (⟨4, by omega⟩, 312934400), (⟨5, by omega⟩, -312934400), (⟨10, by omega⟩, -302448640), (⟨12, by omega⟩, 302448640), (⟨14, by omega⟩, 302448640), (⟨16, by omega⟩, -312934400), (⟨19, by omega⟩, -302448640), (⟨20, by omega⟩, -302448640), (⟨21, by omega⟩, 302448640), (⟨22, by omega⟩, 302448640), (⟨25, by omega⟩, -302448640), (⟨29, by omega⟩, -312934400), (⟨30, by omega⟩, -938803200), (⟨31, by omega⟩, 625868800), (⟨32, by omega⟩, 625868800), (⟨33, by omega⟩, 625868800), (⟨34, by omega⟩, 625868800), (⟨35, by omega⟩, -312934400), (⟨36, by omega⟩, -312934400), (⟨37, by omega⟩, -312934400), (⟨38, by omega⟩, -312934400), (⟨39, by omega⟩, -312934400), (⟨40, by omega⟩, -312934400)]
  claimed := 122709414612958572655411200
}
def branch_box_4004 : RatBox 8 := { lower := box_4004.profileLo, upper := box_4004.profileHi }
def accepted_4004 : Bool := checkAt 527 1000 box_4004 cert_4004

def box_4007 : Box := { S := 818544640, lo := ![0, 603676672, 0, 589607936, 798081024, 0, 798081024, 0], hi := ![20463616, 610711040, 40927232, 596642304, 803196928, 10231808, 808312832, 20463616] }
def cert_4007 : Certificate := {
  mu := [(⟨3, by omega⟩, -74297600), (⟨5, by omega⟩, -525926400), (⟨6, by omega⟩, -292618240), (⟨10, by omega⟩, -525926400), (⟨21, by omega⟩, -233308160), (⟨33, by omega⟩, -292618240), (⟨38, by omega⟩, -525926400), (⟨42, by omega⟩, -525926400), (⟨50, by omega⟩, -525926400), (⟨69, by omega⟩, -233308160), (⟨73, by omega⟩, -525926400), (⟨77, by omega⟩, -292618240), (⟨81, by omega⟩, -525926400), (⟨85, by omega⟩, -292618240), (⟨89, by omega⟩, -1051852800), (⟨94, by omega⟩, -585236480)]
  nu := [(⟨0, by omega⟩, -525926400), (⟨3, by omega⟩, 525926400), (⟨4, by omega⟩, 525926400), (⟨5, by omega⟩, -525926400), (⟨10, by omega⟩, -292618240), (⟨12, by omega⟩, 292618240), (⟨13, by omega⟩, 292618240), (⟨14, by omega⟩, 292618240), (⟨16, by omega⟩, -233308160), (⟨18, by omega⟩, -292618240), (⟨19, by omega⟩, -292618240), (⟨20, by omega⟩, -292618240), (⟨21, by omega⟩, 292618240), (⟨22, by omega⟩, 292618240), (⟨25, by omega⟩, -292618240), (⟨29, by omega⟩, -233308160), (⟨30, by omega⟩, -1577779200), (⟨31, by omega⟩, 1051852800), (⟨32, by omega⟩, 1051852800), (⟨33, by omega⟩, 1051852800), (⟨34, by omega⟩, 1051852800), (⟨35, by omega⟩, -525926400), (⟨36, by omega⟩, -525926400), (⟨37, by omega⟩, -525926400), (⟨38, by omega⟩, -525926400), (⟨39, by omega⟩, -525926400), (⟨40, by omega⟩, -525926400), (⟨41, by omega⟩, -292618240)]
  claimed := 288644753240598413469286400
}
def branch_box_4007 : RatBox 8 := { lower := box_4007.profileLo, upper := box_4007.profileHi }
def accepted_4007 : Bool := checkAt 527 1000 box_4007 cert_4007

def box_4009 : Box := { S := 4040294400, lo := ![0, 2979717120, 0, 2910274560, 3964538880, 0, 3939287040, 0], hi := ![101007360, 3014438400, 202014720, 2944995840, 3989790720, 50503680, 3964538880, 101007360] }
def cert_4009 : Certificate := {
  mu := [(⟨3, by omega⟩, -334910720), (⟨4, by omega⟩, -768122880), (⟨5, by omega⟩, -2577203200), (⟨6, by omega⟩, -1463091200), (⟨10, by omega⟩, -2577203200), (⟨21, by omega⟩, -1114112000), (⟨33, by omega⟩, -1463091200), (⟨38, by omega⟩, -2577203200), (⟨42, by omega⟩, -2577203200), (⟨50, by omega⟩, -2577203200), (⟨53, by omega⟩, -1463091200), (⟨70, by omega⟩, -1463091200), (⟨73, by omega⟩, -2577203200), (⟨77, by omega⟩, -1463091200), (⟨81, by omega⟩, -2577203200), (⟨85, by omega⟩, -1463091200), (⟨89, by omega⟩, -5154406400), (⟨94, by omega⟩, -2926182400)]
  nu := [(⟨0, by omega⟩, -2577203200), (⟨3, by omega⟩, 2577203200), (⟨4, by omega⟩, 2577203200), (⟨5, by omega⟩, -2577203200), (⟨10, by omega⟩, -1463091200), (⟨12, by omega⟩, 1463091200), (⟨13, by omega⟩, 1463091200), (⟨14, by omega⟩, 1463091200), (⟨16, by omega⟩, -1114112000), (⟨18, by omega⟩, -1463091200), (⟨19, by omega⟩, -1463091200), (⟨20, by omega⟩, -1463091200), (⟨21, by omega⟩, 1463091200), (⟨22, by omega⟩, 1463091200), (⟨24, by omega⟩, 1463091200), (⟨25, by omega⟩, -1463091200), (⟨27, by omega⟩, -1463091200), (⟨29, by omega⟩, -1463091200), (⟨30, by omega⟩, -7731609600), (⟨31, by omega⟩, 5154406400), (⟨32, by omega⟩, 5154406400), (⟨33, by omega⟩, 5154406400), (⟨34, by omega⟩, 5154406400), (⟨35, by omega⟩, -2577203200), (⟨36, by omega⟩, -2577203200), (⟨37, by omega⟩, -2577203200), (⟨38, by omega⟩, -2577203200), (⟨39, by omega⟩, -2577203200), (⟨40, by omega⟩, -2577203200), (⟨41, by omega⟩, -1463091200)]
  claimed := 34640872804951098528890880000
}
def branch_box_4009 : RatBox 8 := { lower := box_4009.profileLo, upper := box_4009.profileHi }
def accepted_4009 : Bool := checkAt 527 1000 box_4009 cert_4009

def box_4013 : Box := { S := 30912000, lo := ![0, 22797600, 0, 22531950, 30139200, 0, 30139200, 0], hi := ![772800, 23063250, 1545600, 22797600, 30332400, 386400, 30332400, 772800] }
def cert_4013 : Certificate := {
  mu := [(⟨3, by omega⟩, -3951360), (⟨5, by omega⟩, -15859200), (⟨6, by omega⟩, -15052800), (⟨10, by omega⟩, -15859200), (⟨14, by omega⟩, -15052800), (⟨21, by omega⟩, -15859200), (⟨34, by omega⟩, -15052800), (⟨38, by omega⟩, -15859200), (⟨42, by omega⟩, -15859200), (⟨50, by omega⟩, -15859200), (⟨54, by omega⟩, -3020800), (⟨69, by omega⟩, -15859200), (⟨74, by omega⟩, -15859200), (⟨77, by omega⟩, -1510400), (⟨82, by omega⟩, -15859200), (⟨89, by omega⟩, -31718400)]
  nu := [(⟨0, by omega⟩, -15859200), (⟨3, by omega⟩, 15859200), (⟨4, by omega⟩, 15859200), (⟨5, by omega⟩, -15859200), (⟨10, by omega⟩, -15052800), (⟨11, by omega⟩, 15052800), (⟨12, by omega⟩, 15052800), (⟨13, by omega⟩, 1510400), (⟨15, by omega⟩, -15052800), (⟨16, by omega⟩, -15859200), (⟨18, by omega⟩, -1510400), (⟨20, by omega⟩, -15052800), (⟨21, by omega⟩, 15052800), (⟨22, by omega⟩, 15052800), (⟨24, by omega⟩, 3020800), (⟨25, by omega⟩, -15052800), (⟨27, by omega⟩, -3020800), (⟨29, by omega⟩, -15859200), (⟨30, by omega⟩, -47577600), (⟨31, by omega⟩, 31718400), (⟨32, by omega⟩, 31718400), (⟨33, by omega⟩, 31718400), (⟨34, by omega⟩, 31718400), (⟨35, by omega⟩, -15859200), (⟨36, by omega⟩, -15859200), (⟨37, by omega⟩, -15859200), (⟨38, by omega⟩, -15859200), (⟨39, by omega⟩, -15859200), (⟨40, by omega⟩, -15859200)]
  claimed := 15534688501075968000000
}
def branch_box_4013 : RatBox 8 := { lower := box_4013.profileLo, upper := box_4013.profileHi }
def accepted_4013 : Bool := checkAt 527 1000 box_4013 cert_4013

def box_4016 : Box := { S := 4548198400, lo := ![0, 3373839360, 0, 3315210240, 4434493440, 0, 4462919680, 0], hi := ![113704960, 3393382400, 227409920, 3354296320, 4462919680, 56852480, 4491345920, 113704960] }
def cert_4016 : Certificate := {
  mu := [(⟨3, by omega⟩, -587179520), (⟨5, by omega⟩, -2274099200), (⟨6, by omega⟩, -2274099200), (⟨10, by omega⟩, -2274099200), (⟨13, by omega⟩, -2274099200), (⟨21, by omega⟩, -2274099200), (⟨34, by omega⟩, -2274099200), (⟨38, by omega⟩, -2274099200), (⟨42, by omega⟩, -2274099200), (⟨50, by omega⟩, -2274099200), (⟨61, by omega⟩, -2274099200), (⟨74, by omega⟩, -2274099200), (⟨78, by omega⟩, -629145600), (⟨82, by omega⟩, -2274099200), (⟨90, by omega⟩, -4548198400)]
  nu := [(⟨0, by omega⟩, -2274099200), (⟨3, by omega⟩, 2274099200), (⟨4, by omega⟩, 2274099200), (⟨5, by omega⟩, -2274099200), (⟨10, by omega⟩, -2274099200), (⟨11, by omega⟩, 2274099200), (⟨12, by omega⟩, 2274099200), (⟨13, by omega⟩, 629145600), (⟨15, by omega⟩, -2274099200), (⟨16, by omega⟩, -2274099200), (⟨18, by omega⟩, -629145600), (⟨20, by omega⟩, -2274099200), (⟨21, by omega⟩, 2274099200), (⟨22, by omega⟩, 2274099200), (⟨25, by omega⟩, -2274099200), (⟨28, by omega⟩, -2274099200), (⟨30, by omega⟩, -6822297600), (⟨31, by omega⟩, 4548198400), (⟨32, by omega⟩, 4548198400), (⟨33, by omega⟩, 4548198400), (⟨34, by omega⟩, 4548198400), (⟨35, by omega⟩, -2274099200), (⟨36, by omega⟩, -2274099200), (⟨37, by omega⟩, -2274099200), (⟨38, by omega⟩, -2274099200), (⟨39, by omega⟩, -2274099200), (⟨40, by omega⟩, -2274099200)]
  claimed := 49508601156564212787445760000
}
def branch_box_4016 : RatBox 8 := { lower := box_4016.profileLo, upper := box_4016.profileHi }
def accepted_4016 : Bool := checkAt 527 1000 box_4016 cert_4016

def box_4017 : Box := { S := 24783360, lo := ![0, 18277728, 0, 18064746, 24163776, 0, 24318672, 0], hi := ![619584, 18384219, 1239168, 18277728, 24241224, 309792, 24473568, 619584] }
def cert_4017 : Certificate := {
  mu := [(⟨3, by omega⟩, -3175200), (⟨5, by omega⟩, -12687360), (⟨6, by omega⟩, -12096000), (⟨10, by omega⟩, -12687360), (⟨21, by omega⟩, -12687360), (⟨34, by omega⟩, -12096000), (⟨38, by omega⟩, -12687360), (⟨42, by omega⟩, -12687360), (⟨50, by omega⟩, -12687360), (⟨69, by omega⟩, -12687360), (⟨74, by omega⟩, -12687360), (⟨77, by omega⟩, -1208320), (⟨82, by omega⟩, -12687360), (⟨85, by omega⟩, -2416640), (⟨90, by omega⟩, -25374720)]
  nu := [(⟨0, by omega⟩, -12687360), (⟨3, by omega⟩, 12687360), (⟨4, by omega⟩, 12687360), (⟨5, by omega⟩, -12687360), (⟨10, by omega⟩, -12096000), (⟨12, by omega⟩, 12096000), (⟨13, by omega⟩, 1208320), (⟨14, by omega⟩, 2416640), (⟨16, by omega⟩, -12687360), (⟨18, by omega⟩, -1208320), (⟨19, by omega⟩, -2416640), (⟨20, by omega⟩, -12096000), (⟨21, by omega⟩, 12096000), (⟨22, by omega⟩, 12096000), (⟨25, by omega⟩, -12096000), (⟨29, by omega⟩, -12687360), (⟨30, by omega⟩, -38062080), (⟨31, by omega⟩, 25374720), (⟨32, by omega⟩, 25374720), (⟨33, by omega⟩, 25374720), (⟨34, by omega⟩, 25374720), (⟨35, by omega⟩, -12687360), (⟨36, by omega⟩, -12687360), (⟨37, by omega⟩, -12687360), (⟨38, by omega⟩, -12687360), (⟨39, by omega⟩, -12687360), (⟨40, by omega⟩, -12687360)]
  claimed := 8016065038228075315200
}
def branch_box_4017 : RatBox 8 := { lower := box_4017.profileLo, upper := box_4017.profileHi }
def accepted_4017 : Bool := checkAt 527 1000 box_4017 cert_4017

def box_4019 : Box := { S := 123916800, lo := ![0, 91388640, 0, 90323730, 121206120, 0, 121593360, 0], hi := ![3097920, 91921095, 6195840, 91388640, 121593360, 1548960, 121980600, 3097920] }
def cert_4019 : Certificate := {
  mu := [(⟨3, by omega⟩, -15876000), (⟨5, by omega⟩, -63436800), (⟨6, by omega⟩, -60480000), (⟨10, by omega⟩, -63436800), (⟨21, by omega⟩, -63436800), (⟨34, by omega⟩, -60480000), (⟨38, by omega⟩, -63436800), (⟨42, by omega⟩, -63436800), (⟨50, by omega⟩, -63436800), (⟨69, by omega⟩, -63436800), (⟨74, by omega⟩, -63436800), (⟨77, by omega⟩, -6041600), (⟨82, by omega⟩, -63436800), (⟨85, by omega⟩, -12083200), (⟨89, by omega⟩, -126873600)]
  nu := [(⟨0, by omega⟩, -63436800), (⟨3, by omega⟩, 63436800), (⟨4, by omega⟩, 63436800), (⟨5, by omega⟩, -63436800), (⟨10, by omega⟩, -60480000), (⟨12, by omega⟩, 60480000), (⟨13, by omega⟩, 6041600), (⟨14, by omega⟩, 12083200), (⟨16, by omega⟩, -63436800), (⟨18, by omega⟩, -6041600), (⟨19, by omega⟩, -12083200), (⟨20, by omega⟩, -60480000), (⟨21, by omega⟩, 60480000), (⟨22, by omega⟩, 60480000), (⟨25, by omega⟩, -60480000), (⟨29, by omega⟩, -63436800), (⟨30, by omega⟩, -190310400), (⟨31, by omega⟩, 126873600), (⟨32, by omega⟩, 126873600), (⟨33, by omega⟩, 126873600), (⟨34, by omega⟩, 126873600), (⟨35, by omega⟩, -63436800), (⟨36, by omega⟩, -63436800), (⟨37, by omega⟩, -63436800), (⟨38, by omega⟩, -63436800), (⟨39, by omega⟩, -63436800), (⟨40, by omega⟩, -63436800)]
  claimed := 1002046180393601925120000
}
def branch_box_4019 : RatBox 8 := { lower := box_4019.profileLo, upper := box_4019.profileHi }
def accepted_4019 : Bool := checkAt 527 1000 box_4019 cert_4019

def box_4021 : Box := { S := 1472000, lo := ![0, 1085600, 0, 1072950, 1444400, 0, 1435200, 0], hi := ![36800, 1098250, 73600, 1085600, 1453600, 18400, 1444400, 36800] }
def cert_4021 : Certificate := {
  mu := [(⟨3, by omega⟩, -188160), (⟨4, by omega⟩, -340480), (⟨5, by omega⟩, -755200), (⟨6, by omega⟩, -716800), (⟨10, by omega⟩, -755200), (⟨21, by omega⟩, -755200), (⟨34, by omega⟩, -716800), (⟨38, by omega⟩, -755200), (⟨41, by omega⟩, -755200), (⟨50, by omega⟩, -755200), (⟨54, by omega⟩, -716800), (⟨61, by omega⟩, -38400), (⟨69, by omega⟩, -716800), (⟨73, by omega⟩, -755200), (⟨82, by omega⟩, -755200), (⟨85, by omega⟩, -716800), (⟨90, by omega⟩, -1510400)]
  nu := [(⟨0, by omega⟩, -755200), (⟨3, by omega⟩, 755200), (⟨4, by omega⟩, 755200), (⟨5, by omega⟩, -755200), (⟨10, by omega⟩, -716800), (⟨12, by omega⟩, 716800), (⟨14, by omega⟩, 716800), (⟨16, by omega⟩, -755200), (⟨19, by omega⟩, -716800), (⟨20, by omega⟩, -716800), (⟨21, by omega⟩, 716800), (⟨22, by omega⟩, 716800), (⟨24, by omega⟩, 716800), (⟨25, by omega⟩, -716800), (⟨27, by omega⟩, -716800), (⟨28, by omega⟩, -38400), (⟨29, by omega⟩, -716800), (⟨30, by omega⟩, -2265600), (⟨31, by omega⟩, 1510400), (⟨32, by omega⟩, 1510400), (⟨33, by omega⟩, 1510400), (⟨34, by omega⟩, 1510400), (⟨35, by omega⟩, -755200), (⟨36, by omega⟩, -755200), (⟨37, by omega⟩, -755200), (⟨38, by omega⟩, -755200), (⟨39, by omega⟩, -755200), (⟨40, by omega⟩, -755200)]
  claimed := 1677431001088000000
}
def branch_box_4021 : RatBox 8 := { lower := box_4021.profileLo, upper := box_4021.profileHi }
def accepted_4021 : Bool := checkAt 527 1000 box_4021 cert_4021

def box_4024 : Box := { S := 1113305907200, lo := ![0, 825846842880, 0, 811495633920, 1092431421440, 0, 1092431421440, 0], hi := ![27832647680, 830630579200, 55665295360, 821063106560, 1099389583360, 13916323840, 1099389583360, 27832647680] }
def cert_4024 : Certificate := {
  mu := [(⟨3, by omega⟩, -269562780160), (⟨5, by omega⟩, -69310873600), (⟨6, by omega⟩, -1043995033600), (⟨10, by omega⟩, -69310873600), (⟨13, by omega⟩, -1113305907200), (⟨34, by omega⟩, -1043995033600), (⟨38, by omega⟩, -69310873600), (⟨42, by omega⟩, -69310873600), (⟨50, by omega⟩, -69310873600), (⟨54, by omega⟩, -13421772800), (⟨69, by omega⟩, -69310873600), (⟨74, by omega⟩, -69310873600), (⟨82, by omega⟩, -69310873600), (⟨89, by omega⟩, -1043995033600), (⟨90, by omega⟩, -1043995033600)]
  nu := [(⟨0, by omega⟩, -1043995033600), (⟨3, by omega⟩, 1043995033600), (⟨4, by omega⟩, 1043995033600), (⟨5, by omega⟩, -69310873600), (⟨10, by omega⟩, -1043995033600), (⟨11, by omega⟩, 1043995033600), (⟨12, by omega⟩, 1043995033600), (⟨15, by omega⟩, -1113305907200), (⟨20, by omega⟩, -1043995033600), (⟨21, by omega⟩, 1043995033600), (⟨22, by omega⟩, 1043995033600), (⟨24, by omega⟩, 13421772800), (⟨25, by omega⟩, -1043995033600), (⟨27, by omega⟩, -13421772800), (⟨29, by omega⟩, -69310873600), (⟨30, by omega⟩, -1182616780800), (⟨31, by omega⟩, 138621747200), (⟨32, by omega⟩, 138621747200), (⟨33, by omega⟩, 1113305907200), (⟨34, by omega⟩, 1113305907200), (⟨35, by omega⟩, -69310873600), (⟨36, by omega⟩, -69310873600), (⟨37, by omega⟩, -69310873600), (⟨38, by omega⟩, -69310873600), (⟨39, by omega⟩, -69310873600), (⟨40, by omega⟩, -1043995033600)]
  claimed := 726436116229177676650749529948160000
}
def branch_box_4024 : RatBox 8 := { lower := box_4024.profileLo, upper := box_4024.profileHi }
def accepted_4024 : Bool := checkAt 527 1000 box_4024 cert_4024

def box_4030 : Box := { S := 8316518400, lo := ![0, 6169167360, 0, 6061962240, 8108605440, 0, 8212561920, 0], hi := ![207912960, 6204902400, 415825920, 6133432320, 8212561920, 103956480, 8316518400, 207912960] }
def cert_4030 : Certificate := {
  mu := [(⟨3, by omega⟩, -2039052800), (⟨5, by omega⟩, -419430400), (⟨6, by omega⟩, -7897088000), (⟨10, by omega⟩, -419430400), (⟨34, by omega⟩, -7897088000), (⟨38, by omega⟩, -419430400), (⟨42, by omega⟩, -419430400), (⟨50, by omega⟩, -419430400), (⟨69, by omega⟩, -419430400), (⟨74, by omega⟩, -419430400), (⟨82, by omega⟩, -419430400), (⟨86, by omega⟩, -8316518400), (⟨89, by omega⟩, -15794176000)]
  nu := [(⟨0, by omega⟩, -7897088000), (⟨3, by omega⟩, 7897088000), (⟨4, by omega⟩, 7897088000), (⟨5, by omega⟩, -419430400), (⟨10, by omega⟩, -7897088000), (⟨12, by omega⟩, 7897088000), (⟨14, by omega⟩, 7897088000), (⟨19, by omega⟩, -8316518400), (⟨20, by omega⟩, -7897088000), (⟨21, by omega⟩, 7897088000), (⟨22, by omega⟩, 7897088000), (⟨25, by omega⟩, -7897088000), (⟨29, by omega⟩, -419430400), (⟨30, by omega⟩, -8735948800), (⟨31, by omega⟩, 838860800), (⟨32, by omega⟩, 838860800), (⟨33, by omega⟩, 8316518400), (⟨34, by omega⟩, 8316518400), (⟨35, by omega⟩, -419430400), (⟨36, by omega⟩, -419430400), (⟨37, by omega⟩, -419430400), (⟨38, by omega⟩, -419430400), (⟨39, by omega⟩, -419430400), (⟨40, by omega⟩, -7897088000)]
  claimed := 302797775033856008399093760000
}
def branch_box_4030 : RatBox 8 := { lower := box_4030.profileLo, upper := box_4030.profileHi }
def accepted_4030 : Bool := checkAt 527 1000 box_4030 cert_4030

def box_4032 : Box := { S := 819200, lo := ![0, 611200, 0, 597120, 798720, 0, 808960, 0], hi := ![20480, 618240, 40960, 604160, 808960, 10240, 819200, 20480] }
def cert_4032 : Certificate := {
  mu := [(⟨3, by omega⟩, -208000), (⟨6, by omega⟩, -819200), (⟨13, by omega⟩, -819200), (⟨21, by omega⟩, -819200), (⟨34, by omega⟩, -819200), (⟨78, by omega⟩, -819200), (⟨89, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -819200), (⟨3, by omega⟩, 819200), (⟨4, by omega⟩, 819200), (⟨10, by omega⟩, -819200), (⟨11, by omega⟩, 819200), (⟨12, by omega⟩, 819200), (⟨13, by omega⟩, 819200), (⟨15, by omega⟩, -819200), (⟨16, by omega⟩, -819200), (⟨18, by omega⟩, -819200), (⟨20, by omega⟩, -819200), (⟨21, by omega⟩, 819200), (⟨22, by omega⟩, 819200), (⟨25, by omega⟩, -819200), (⟨30, by omega⟩, -819200), (⟨33, by omega⟩, 819200), (⟨34, by omega⟩, 819200), (⟨40, by omega⟩, -819200)]
  claimed := 286566257786880000
}
def branch_box_4032 : RatBox 8 := { lower := box_4032.profileLo, upper := box_4032.profileHi }
def accepted_4032 : Bool := checkAt 527 1000 box_4032 cert_4032

def box_4034 : Box := { S := 6553600, lo := ![0, 4917760, 0, 4720640, 6389760, 0, 6471680, 0], hi := ![163840, 4945920, 327680, 4776960, 6471680, 81920, 6553600, 163840] }
def cert_4034 : Certificate := {
  mu := [(⟨3, by omega⟩, -1635840), (⟨6, by omega⟩, -6553600), (⟨34, by omega⟩, -6553600), (⟨86, by omega⟩, -6553600), (⟨89, by omega⟩, -13107200)]
  nu := [(⟨0, by omega⟩, -6553600), (⟨3, by omega⟩, 6553600), (⟨4, by omega⟩, 6553600), (⟨10, by omega⟩, -6553600), (⟨12, by omega⟩, 6553600), (⟨14, by omega⟩, 6553600), (⟨19, by omega⟩, -6553600), (⟨20, by omega⟩, -6553600), (⟨21, by omega⟩, 6553600), (⟨22, by omega⟩, 6553600), (⟨25, by omega⟩, -6553600), (⟨30, by omega⟩, -6553600), (⟨33, by omega⟩, 6553600), (⟨34, by omega⟩, 6553600), (⟨40, by omega⟩, -6553600)]
  claimed := 147046494665441280000
}
def branch_box_4034 : RatBox 8 := { lower := box_4034.profileLo, upper := box_4034.profileHi }
def accepted_4034 : Bool := checkAt 527 1000 box_4034 cert_4034

def box_4040 : Box := { S := 1310720, lo := ![0, 972288, 0, 955392, 1294336, 0, 1277952, 0], hi := ![32768, 977920, 65536, 966656, 1310720, 16384, 1310720, 32768] }
def cert_4040 : Certificate := {
  mu := [(⟨3, by omega⟩, -338432), (⟨4, by omega⟩, -32768), (⟨6, by omega⟩, -1310720), (⟨34, by omega⟩, -1310720), (⟨86, by omega⟩, -1310720), (⟨90, by omega⟩, -2621440)]
  nu := [(⟨0, by omega⟩, -1310720), (⟨3, by omega⟩, 1310720), (⟨4, by omega⟩, 1310720), (⟨10, by omega⟩, -1310720), (⟨12, by omega⟩, 1310720), (⟨14, by omega⟩, 1310720), (⟨19, by omega⟩, -1310720), (⟨20, by omega⟩, -1310720), (⟨21, by omega⟩, 1310720), (⟨22, by omega⟩, 1310720), (⟨25, by omega⟩, -1310720), (⟨30, by omega⟩, -1310720), (⟨33, by omega⟩, 1310720), (⟨34, by omega⟩, 1310720), (⟨40, by omega⟩, -1310720)]
  claimed := 1185079402220748800
}
def branch_box_4040 : RatBox 8 := { lower := box_4040.profileLo, upper := box_4040.profileHi }
def accepted_4040 : Bool := checkAt 527 1000 box_4040 cert_4040

def box_4042 : Box := { S := 819200, lo := ![0, 611200, 0, 597120, 808960, 0, 798720, 0], hi := ![20480, 618240, 40960, 604160, 819200, 10240, 819200, 20480] }
def cert_4042 : Certificate := {
  mu := [(⟨3, by omega⟩, -208000), (⟨4, by omega⟩, -20480), (⟨6, by omega⟩, -819200), (⟨34, by omega⟩, -819200), (⟨86, by omega⟩, -819200), (⟨90, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -819200), (⟨3, by omega⟩, 819200), (⟨4, by omega⟩, 819200), (⟨10, by omega⟩, -819200), (⟨12, by omega⟩, 819200), (⟨14, by omega⟩, 819200), (⟨19, by omega⟩, -819200), (⟨20, by omega⟩, -819200), (⟨21, by omega⟩, 819200), (⟨22, by omega⟩, 819200), (⟨25, by omega⟩, -819200), (⟨30, by omega⟩, -819200), (⟨33, by omega⟩, 819200), (⟨34, by omega⟩, 819200), (⟨40, by omega⟩, -819200)]
  claimed := 286394459095040000
}
def branch_box_4042 : RatBox 8 := { lower := box_4042.profileLo, upper := box_4042.profileHi }
def accepted_4042 : Bool := checkAt 527 1000 box_4042 cert_4042

def box_4044 : Box := { S := 2517893120, lo := ![0, 1889403392, 0, 1813669888, 2486419456, 0, 2454945792, 0], hi := ![62947328, 1900222464, 125894656, 1835308032, 2517893120, 31473664, 2517893120, 62947328] }
def cert_4044 : Certificate := {
  mu := [(⟨3, by omega⟩, -628489728), (⟨4, by omega⟩, -62947328), (⟨6, by omega⟩, -2517893120), (⟨34, by omega⟩, -2517893120), (⟨54, by omega⟩, -854589440), (⟨86, by omega⟩, -2517893120), (⟨90, by omega⟩, -5035786240)]
  nu := [(⟨0, by omega⟩, -2517893120), (⟨3, by omega⟩, 2517893120), (⟨4, by omega⟩, 2517893120), (⟨10, by omega⟩, -2517893120), (⟨12, by omega⟩, 2517893120), (⟨14, by omega⟩, 2517893120), (⟨19, by omega⟩, -2517893120), (⟨20, by omega⟩, -2517893120), (⟨21, by omega⟩, 2517893120), (⟨22, by omega⟩, 2517893120), (⟨25, by omega⟩, -2517893120), (⟨27, by omega⟩, -854589440), (⟨30, by omega⟩, -2517893120), (⟨33, by omega⟩, 2517893120), (⟨34, by omega⟩, 2517893120), (⟨40, by omega⟩, -2517893120)]
  claimed := 8334257062932004302592409600
}
def branch_box_4044 : RatBox 8 := { lower := box_4044.profileLo, upper := box_4044.profileHi }
def accepted_4044 : Bool := checkAt 527 1000 box_4044 cert_4044

def box_4046 : Box := { S := 15820800, lo := ![0, 11667840, 0, 11395920, 15425280, 197760, 15425280, 197760], hi := ![395520, 11939760, 791040, 11667840, 15820800, 395520, 15820800, 395520] }
def cert_4046 : Certificate := {
  mu := [(⟨3, by omega⟩, -3562880), (⟨5, by omega⟩, -819200), (⟨6, by omega⟩, -15001600), (⟨10, by omega⟩, -819200), (⟨13, by omega⟩, -15001600), (⟨21, by omega⟩, -15001600), (⟨29, by omega⟩, -15001600), (⟨34, by omega⟩, -15001600), (⟨37, by omega⟩, -819200), (⟨42, by omega⟩, -819200), (⟨45, by omega⟩, -15001600), (⟨50, by omega⟩, -819200), (⟨53, by omega⟩, -15001600), (⟨61, by omega⟩, -15001600), (⟨69, by omega⟩, -15001600), (⟨74, by omega⟩, -819200), (⟨77, by omega⟩, -15001600), (⟨82, by omega⟩, -819200), (⟨85, by omega⟩, -15001600), (⟨89, by omega⟩, -15001600), (⟨90, by omega⟩, -15001600), (⟨93, by omega⟩, -30003200)]
  nu := [(⟨0, by omega⟩, -15001600), (⟨3, by omega⟩, 15001600), (⟨4, by omega⟩, 15001600), (⟨5, by omega⟩, -819200), (⟨10, by omega⟩, -15001600), (⟨11, by omega⟩, 15001600), (⟨12, by omega⟩, 15001600), (⟨13, by omega⟩, 15001600), (⟨14, by omega⟩, 15001600), (⟨15, by omega⟩, -15001600), (⟨16, by omega⟩, -15001600), (⟨17, by omega⟩, -15001600), (⟨18, by omega⟩, -15001600), (⟨19, by omega⟩, -15001600), (⟨20, by omega⟩, -15001600), (⟨21, by omega⟩, 15001600), (⟨22, by omega⟩, 15001600), (⟨23, by omega⟩, 15001600), (⟨24, by omega⟩, 15001600), (⟨25, by omega⟩, -15001600), (⟨26, by omega⟩, -15001600), (⟨27, by omega⟩, -15001600), (⟨28, by omega⟩, -15001600), (⟨29, by omega⟩, -15001600), (⟨30, by omega⟩, -16640000), (⟨31, by omega⟩, 1638400), (⟨32, by omega⟩, 1638400), (⟨33, by omega⟩, 15820800), (⟨34, by omega⟩, 15820800), (⟨35, by omega⟩, -819200), (⟨36, by omega⟩, -819200), (⟨37, by omega⟩, -819200), (⟨38, by omega⟩, -819200), (⟨39, by omega⟩, -819200), (⟨40, by omega⟩, -15001600), (⟨41, by omega⟩, -15001600)]
  claimed := 2079716936287518720000
}
def branch_box_4046 : RatBox 8 := { lower := box_4046.profileLo, upper := box_4046.profileHi }
def accepted_4046 : Bool := checkAt 527 1000 box_4046 cert_4046

def box_4049 : Box := { S := 310400, lo := ![0, 228920, 0, 223585, 302640, 3880, 302640, 0], hi := ![7760, 234255, 15520, 228920, 306520, 7760, 306520, 3880] }
def cert_4049 : Certificate := {
  mu := [(⟨3, by omega⟩, -36520), (⟨4, by omega⟩, -72000), (⟨5, by omega⟩, -160000), (⟨6, by omega⟩, -150400), (⟨10, by omega⟩, -160000), (⟨21, by omega⟩, -9600), (⟨34, by omega⟩, -150400), (⟨38, by omega⟩, -160000), (⟨42, by omega⟩, -160000), (⟨45, by omega⟩, -150400), (⟨50, by omega⟩, -160000), (⟨54, by omega⟩, -150400), (⟨61, by omega⟩, -150400), (⟨69, by omega⟩, -64000), (⟨70, by omega⟩, -86400), (⟨73, by omega⟩, -160000), (⟨77, by omega⟩, -150400), (⟨82, by omega⟩, -160000), (⟨85, by omega⟩, -150400), (⟨90, by omega⟩, -320000), (⟨94, by omega⟩, -300800)]
  nu := [(⟨0, by omega⟩, -160000), (⟨3, by omega⟩, 160000), (⟨4, by omega⟩, 160000), (⟨5, by omega⟩, -160000), (⟨10, by omega⟩, -150400), (⟨12, by omega⟩, 150400), (⟨13, by omega⟩, 150400), (⟨14, by omega⟩, 150400), (⟨16, by omega⟩, -9600), (⟨18, by omega⟩, -150400), (⟨19, by omega⟩, -150400), (⟨20, by omega⟩, -150400), (⟨21, by omega⟩, 150400), (⟨22, by omega⟩, 150400), (⟨23, by omega⟩, 150400), (⟨24, by omega⟩, 150400), (⟨25, by omega⟩, -150400), (⟨26, by omega⟩, -150400), (⟨27, by omega⟩, -150400), (⟨28, by omega⟩, -150400), (⟨29, by omega⟩, -150400), (⟨30, by omega⟩, -480000), (⟨31, by omega⟩, 320000), (⟨32, by omega⟩, 320000), (⟨33, by omega⟩, 320000), (⟨34, by omega⟩, 320000), (⟨35, by omega⟩, -160000), (⟨36, by omega⟩, -160000), (⟨37, by omega⟩, -160000), (⟨38, by omega⟩, -160000), (⟨39, by omega⟩, -160000), (⟨40, by omega⟩, -160000), (⟨41, by omega⟩, -150400)]
  claimed := 15632296263680000
}
def branch_box_4049 : RatBox 8 := { lower := box_4049.profileLo, upper := box_4049.profileHi }
def accepted_4049 : Bool := checkAt 527 1000 box_4049 cert_4049

end PeaceableQueens.UpperBound.Generated.Even.Core
