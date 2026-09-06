import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_1302 : Box := { S := 230798131200, lo := ![0, 149387696640, 0, 191039546880, 227913154560, 0, 225028177920, 0], hi := ![5769953280, 150379407360, 11539906560, 192031257600, 230798131200, 2884976640, 230798131200, 5769953280] }
def cert_1302 : Certificate := {
  mu := [(⟨4, by omega⟩, -2811002880), (⟨5, by omega⟩, -5917900800), (⟨6, by omega⟩, -224880230400), (⟨9, by omega⟩, -5917900800), (⟨13, by omega⟩, -224880230400), (⟨22, by omega⟩, -5917900800), (⟨34, by omega⟩, -224880230400), (⟨37, by omega⟩, -5917900800), (⟨42, by omega⟩, -5917900800), (⟨50, by omega⟩, -5917900800), (⟨54, by omega⟩, -7969177600), (⟨70, by omega⟩, -7969177600), (⟨74, by omega⟩, -5917900800), (⟨82, by omega⟩, -5917900800), (⟨90, by omega⟩, -449760460800)]
  nu := [(⟨0, by omega⟩, -224880230400), (⟨3, by omega⟩, 224880230400), (⟨4, by omega⟩, 224880230400), (⟨5, by omega⟩, -5917900800), (⟨10, by omega⟩, -224880230400), (⟨11, by omega⟩, 224880230400), (⟨12, by omega⟩, 224880230400), (⟨15, by omega⟩, -224880230400), (⟨16, by omega⟩, -5917900800), (⟨20, by omega⟩, -224880230400), (⟨21, by omega⟩, 224880230400), (⟨22, by omega⟩, 224880230400), (⟨24, by omega⟩, 7969177600), (⟨25, by omega⟩, -224880230400), (⟨27, by omega⟩, -7969177600), (⟨29, by omega⟩, -7969177600), (⟨30, by omega⟩, -236716032000), (⟨31, by omega⟩, 11835801600), (⟨32, by omega⟩, 11835801600), (⟨33, by omega⟩, 230798131200), (⟨34, by omega⟩, 230798131200), (⟨35, by omega⟩, -5917900800), (⟨36, by omega⟩, -5917900800), (⟨37, by omega⟩, -5917900800), (⟨38, by omega⟩, -5917900800), (⟨39, by omega⟩, -5917900800), (⟨40, by omega⟩, -224880230400)]
  claimed := 6457797496228568907054537768960000
}
def branch_box_1302 : RatBox 8 := { lower := box_1302.profileLo, upper := box_1302.profileHi }
def accepted_1302 : Bool := checkAt 527 1000 box_1302 cert_1302

def box_1304 : Box := { S := 925696000, lo := ![0, 603148800, 0, 762252800, 902553600, 0, 902553600, 0], hi := ![23142400, 619059200, 46284800, 778163200, 925696000, 23142400, 925696000, 23142400] }
def cert_1304 : Certificate := {
  mu := [(⟨5, by omega⟩, -46284800), (⟨6, by omega⟩, -879411200), (⟨9, by omega⟩, -46284800), (⟨21, by omega⟩, -46284800), (⟨34, by omega⟩, -46284800), (⟨37, by omega⟩, -46284800), (⟨42, by omega⟩, -46284800), (⟨50, by omega⟩, -46284800), (⟨54, by omega⟩, -879411200), (⟨69, by omega⟩, -46284800), (⟨74, by omega⟩, -46284800), (⟨78, by omega⟩, -6553600), (⟨82, by omega⟩, -46284800), (⟨89, by omega⟩, -879411200), (⟨90, by omega⟩, -879411200)]
  nu := [(⟨0, by omega⟩, -879411200), (⟨3, by omega⟩, 879411200), (⟨4, by omega⟩, 879411200), (⟨5, by omega⟩, -46284800), (⟨10, by omega⟩, -879411200), (⟨12, by omega⟩, 879411200), (⟨13, by omega⟩, 6553600), (⟨16, by omega⟩, -46284800), (⟨18, by omega⟩, -6553600), (⟨20, by omega⟩, -879411200), (⟨21, by omega⟩, 879411200), (⟨22, by omega⟩, 46284800), (⟨24, by omega⟩, 879411200), (⟨25, by omega⟩, -46284800), (⟨27, by omega⟩, -879411200), (⟨29, by omega⟩, -46284800), (⟨30, by omega⟩, -971980800), (⟨31, by omega⟩, 92569600), (⟨32, by omega⟩, 92569600), (⟨33, by omega⟩, 925696000), (⟨34, by omega⟩, 925696000), (⟨35, by omega⟩, -46284800), (⟨36, by omega⟩, -46284800), (⟨37, by omega⟩, -46284800), (⟨38, by omega⟩, -46284800), (⟨39, by omega⟩, -46284800), (⟨40, by omega⟩, -879411200)]
  claimed := 416908478992091185152000000
}
def branch_box_1304 : RatBox 8 := { lower := box_1304.profileLo, upper := box_1304.profileHi }
def accepted_1304 : Bool := checkAt 527 1000 box_1304 cert_1304

def box_1306 : Box := { S := 87850444800, lo := ![0, 57240055440, 0, 70829421120, 85654183680, 1098130560, 85654183680, 0], hi := ![2196261120, 58749984960, 4392522240, 72339350640, 87850444800, 2196261120, 87850444800, 2196261120] }
def cert_1306 : Certificate := {
  mu := [(⟨4, by omega⟩, -20710722960), (⟨5, by omega⟩, -47805542400), (⟨6, by omega⟩, -40044902400), (⟨9, by omega⟩, -47805542400), (⟨13, by omega⟩, -40044902400), (⟨21, by omega⟩, -40044902400), (⟨30, by omega⟩, -40044902400), (⟨33, by omega⟩, -4068556800), (⟨37, by omega⟩, -47805542400), (⟨42, by omega⟩, -47805542400), (⟨45, by omega⟩, -40044902400), (⟨54, by omega⟩, -40044902400), (⟨61, by omega⟩, -4068556800), (⟨70, by omega⟩, -4068556800), (⟨74, by omega⟩, -47805542400), (⟨77, by omega⟩, -40044902400), (⟨79, by omega⟩, -24661990400), (⟨86, by omega⟩, -40044902400), (⟨89, by omega⟩, -47010076800), (⟨90, by omega⟩, -33079728000), (⟨94, by omega⟩, -80089804800)]
  nu := [(⟨0, by omega⟩, -40044902400), (⟨3, by omega⟩, 40044902400), (⟨4, by omega⟩, 40044902400), (⟨5, by omega⟩, -47805542400), (⟨10, by omega⟩, -40044902400), (⟨11, by omega⟩, 40044902400), (⟨12, by omega⟩, 40044902400), (⟨13, by omega⟩, 40044902400), (⟨14, by omega⟩, 40044902400), (⟨15, by omega⟩, -40044902400), (⟨16, by omega⟩, -40044902400), (⟨17, by omega⟩, -40044902400), (⟨18, by omega⟩, -40044902400), (⟨19, by omega⟩, -40044902400), (⟨20, by omega⟩, -40044902400), (⟨21, by omega⟩, 40044902400), (⟨22, by omega⟩, 4068556800), (⟨23, by omega⟩, 40044902400), (⟨24, by omega⟩, 40044902400), (⟨25, by omega⟩, -4068556800), (⟨26, by omega⟩, -40044902400), (⟨27, by omega⟩, -40044902400), (⟨28, by omega⟩, -4068556800), (⟨29, by omega⟩, -4068556800), (⟨30, by omega⟩, -87850444800), (⟨31, by omega⟩, 47805542400), (⟨32, by omega⟩, 23143552000), (⟨33, by omega⟩, 87850444800), (⟨34, by omega⟩, 40044902400), (⟨35, by omega⟩, -47805542400), (⟨36, by omega⟩, -47805542400), (⟨38, by omega⟩, -47805542400), (⟨39, by omega⟩, 24661990400), (⟨40, by omega⟩, -40044902400), (⟨41, by omega⟩, -40044902400)]
  claimed := 357290019805540757667674849280000
}
def branch_box_1306 : RatBox 8 := { lower := box_1306.profileLo, upper := box_1306.profileHi }
def accepted_1306 : Bool := checkAt 527 1000 box_1306 cert_1306

def box_1309 : Box := { S := 9667200, lo := ![0, 6298785, 0, 7794180, 9425520, 0, 9425520, 0], hi := ![241680, 6464940, 483360, 7960335, 9546360, 120840, 9546360, 241680] }
def cert_1309 : Certificate := {
  mu := [(⟨5, by omega⟩, -5427200), (⟨6, by omega⟩, -4240000), (⟨9, by omega⟩, -5427200), (⟨21, by omega⟩, -5427200), (⟨33, by omega⟩, -4240000), (⟨37, by omega⟩, -5427200), (⟨42, by omega⟩, -5427200), (⟨45, by omega⟩, -409600), (⟨50, by omega⟩, -5427200), (⟨62, by omega⟩, -5427200), (⟨74, by omega⟩, -5427200), (⟨82, by omega⟩, -5427200), (⟨89, by omega⟩, -10854400)]
  nu := [(⟨0, by omega⟩, -5427200), (⟨3, by omega⟩, 5427200), (⟨4, by omega⟩, 5427200), (⟨5, by omega⟩, -5427200), (⟨10, by omega⟩, -4240000), (⟨12, by omega⟩, 4240000), (⟨16, by omega⟩, -5427200), (⟨20, by omega⟩, -4240000), (⟨21, by omega⟩, 4240000), (⟨22, by omega⟩, 4240000), (⟨23, by omega⟩, 409600), (⟨25, by omega⟩, -4240000), (⟨26, by omega⟩, -409600), (⟨28, by omega⟩, -5427200), (⟨30, by omega⟩, -16281600), (⟨31, by omega⟩, 10854400), (⟨32, by omega⟩, 10854400), (⟨33, by omega⟩, 10854400), (⟨34, by omega⟩, 10854400), (⟨35, by omega⟩, -5427200), (⟨36, by omega⟩, -5427200), (⟨37, by omega⟩, -5427200), (⟨38, by omega⟩, -5427200), (⟨39, by omega⟩, -5427200), (⟨40, by omega⟩, -5427200)]
  claimed := 475636484571586560000
}
def branch_box_1309 : RatBox 8 := { lower := box_1309.profileLo, upper := box_1309.profileHi }
def accepted_1309 : Bool := checkAt 527 1000 box_1309 cert_1309

def box_1318 : Box := { S := 131072000, lo := ![0, 85964800, 0, 107366400, 127795200, 0, 129433600, 0], hi := ![3276800, 86528000, 6553600, 107929600, 129433600, 1638400, 131072000, 3276800] }
def cert_1318 : Certificate := {
  mu := [(⟨5, by omega⟩, -6553600), (⟨6, by omega⟩, -124518400), (⟨9, by omega⟩, -6553600), (⟨13, by omega⟩, -131072000), (⟨34, by omega⟩, -131072000), (⟨37, by omega⟩, -6553600), (⟨42, by omega⟩, -6553600), (⟨50, by omega⟩, -6553600), (⟨74, by omega⟩, -6553600), (⟨82, by omega⟩, -6553600), (⟨89, by omega⟩, -249036800)]
  nu := [(⟨0, by omega⟩, -124518400), (⟨3, by omega⟩, 124518400), (⟨4, by omega⟩, 124518400), (⟨5, by omega⟩, -6553600), (⟨10, by omega⟩, -124518400), (⟨11, by omega⟩, 124518400), (⟨12, by omega⟩, 124518400), (⟨15, by omega⟩, -131072000), (⟨20, by omega⟩, -124518400), (⟨21, by omega⟩, 124518400), (⟨22, by omega⟩, 124518400), (⟨25, by omega⟩, -131072000), (⟨30, by omega⟩, -137625600), (⟨31, by omega⟩, 13107200), (⟨32, by omega⟩, 13107200), (⟨33, by omega⟩, 131072000), (⟨34, by omega⟩, 131072000), (⟨35, by omega⟩, -6553600), (⟨36, by omega⟩, -6553600), (⟨37, by omega⟩, -6553600), (⟨38, by omega⟩, -6553600), (⟨39, by omega⟩, -6553600), (⟨40, by omega⟩, -124518400)]
  claimed := 1182904619760615424000000
}
def branch_box_1318 : RatBox 8 := { lower := box_1318.profileLo, upper := box_1318.profileHi }
def accepted_1318 : Bool := checkAt 527 1000 box_1318 cert_1318

def box_1320 : Box := { S := 32768000, lo := ![0, 21632000, 0, 26700800, 31948800, 0, 32358400, 0], hi := ![819200, 21913600, 1638400, 26982400, 32358400, 409600, 32768000, 819200] }
def cert_1320 : Certificate := {
  mu := [(⟨5, by omega⟩, -1638400), (⟨6, by omega⟩, -31129600), (⟨9, by omega⟩, -1638400), (⟨13, by omega⟩, -32768000), (⟨34, by omega⟩, -32768000), (⟨37, by omega⟩, -1638400), (⟨42, by omega⟩, -1638400), (⟨50, by omega⟩, -1638400), (⟨74, by omega⟩, -1638400), (⟨82, by omega⟩, -1638400), (⟨89, by omega⟩, -62259200)]
  nu := [(⟨0, by omega⟩, -31129600), (⟨3, by omega⟩, 31129600), (⟨4, by omega⟩, 31129600), (⟨5, by omega⟩, -1638400), (⟨10, by omega⟩, -31129600), (⟨11, by omega⟩, 31129600), (⟨12, by omega⟩, 31129600), (⟨15, by omega⟩, -32768000), (⟨20, by omega⟩, -31129600), (⟨21, by omega⟩, 31129600), (⟨22, by omega⟩, 31129600), (⟨25, by omega⟩, -32768000), (⟨30, by omega⟩, -34406400), (⟨31, by omega⟩, 3276800), (⟨32, by omega⟩, 3276800), (⟨33, by omega⟩, 32768000), (⟨34, by omega⟩, 32768000), (⟨35, by omega⟩, -1638400), (⟨36, by omega⟩, -1638400), (⟨37, by omega⟩, -1638400), (⟨38, by omega⟩, -1638400), (⟨39, by omega⟩, -1638400), (⟨40, by omega⟩, -31129600)]
  claimed := 18484086469296128000000
}
def branch_box_1320 : RatBox 8 := { lower := box_1320.profileLo, upper := box_1320.profileHi }
def accepted_1320 : Bool := checkAt 527 1000 box_1320 cert_1320

def box_1324 : Box := { S := 131072000, lo := ![0, 87091200, 0, 106240000, 127795200, 0, 129433600, 0], hi := ![3276800, 87654400, 6553600, 106803200, 129433600, 1638400, 131072000, 3276800] }
def cert_1324 : Certificate := {
  mu := [(⟨5, by omega⟩, -6553600), (⟨6, by omega⟩, -124518400), (⟨9, by omega⟩, -6553600), (⟨13, by omega⟩, -131072000), (⟨34, by omega⟩, -131072000), (⟨37, by omega⟩, -6553600), (⟨42, by omega⟩, -6553600), (⟨50, by omega⟩, -6553600), (⟨74, by omega⟩, -6553600), (⟨82, by omega⟩, -6553600), (⟨89, by omega⟩, -249036800)]
  nu := [(⟨0, by omega⟩, -124518400), (⟨3, by omega⟩, 124518400), (⟨4, by omega⟩, 124518400), (⟨5, by omega⟩, -6553600), (⟨10, by omega⟩, -124518400), (⟨11, by omega⟩, 124518400), (⟨12, by omega⟩, 124518400), (⟨15, by omega⟩, -131072000), (⟨20, by omega⟩, -124518400), (⟨21, by omega⟩, 124518400), (⟨22, by omega⟩, 124518400), (⟨25, by omega⟩, -131072000), (⟨30, by omega⟩, -137625600), (⟨31, by omega⟩, 13107200), (⟨32, by omega⟩, 13107200), (⟨33, by omega⟩, 131072000), (⟨34, by omega⟩, 131072000), (⟨35, by omega⟩, -6553600), (⟨36, by omega⟩, -6553600), (⟨37, by omega⟩, -6553600), (⟨38, by omega⟩, -6553600), (⟨39, by omega⟩, -6553600), (⟨40, by omega⟩, -124518400)]
  claimed := 1183054290780946432000000
}
def branch_box_1324 : RatBox 8 := { lower := box_1324.profileLo, upper := box_1324.profileHi }
def accepted_1324 : Bool := checkAt 527 1000 box_1324 cert_1324

def box_1332 : Box := { S := 11276800, lo := ![0, 7395995, 0, 9237285, 11135840, 0, 10994880, 0], hi := ![281920, 7444450, 563840, 9285740, 11276800, 140960, 11276800, 281920] }
def cert_1332 : Certificate := {
  mu := [(⟨4, by omega⟩, -281920), (⟨6, by omega⟩, -11276800), (⟨13, by omega⟩, -11276800), (⟨34, by omega⟩, -11276800), (⟨54, by omega⟩, -819200), (⟨70, by omega⟩, -819200), (⟨90, by omega⟩, -22553600)]
  nu := [(⟨0, by omega⟩, -11276800), (⟨3, by omega⟩, 11276800), (⟨4, by omega⟩, 11276800), (⟨10, by omega⟩, -11276800), (⟨11, by omega⟩, 11276800), (⟨12, by omega⟩, 11276800), (⟨15, by omega⟩, -11276800), (⟨20, by omega⟩, -11276800), (⟨21, by omega⟩, 11276800), (⟨22, by omega⟩, 11276800), (⟨24, by omega⟩, 819200), (⟨25, by omega⟩, -11276800), (⟨27, by omega⟩, -819200), (⟨29, by omega⟩, -819200), (⟨30, by omega⟩, -11276800), (⟨33, by omega⟩, 11276800), (⟨34, by omega⟩, 11276800), (⟨40, by omega⟩, -11276800)]
  claimed := 753312838923714560000
}
def branch_box_1332 : RatBox 8 := { lower := box_1332.profileLo, upper := box_1332.profileHi }
def accepted_1332 : Bool := checkAt 527 1000 box_1332 cert_1332

def box_1334 : Box := { S := 556800, lo := ![0, 367575, 0, 453705, 549840, 0, 542880, 0], hi := ![13920, 372360, 27840, 458490, 556800, 6960, 556800, 13920] }
def cert_1334 : Certificate := {
  mu := [(⟨4, by omega⟩, -13920), (⟨6, by omega⟩, -556800), (⟨13, by omega⟩, -556800), (⟨34, by omega⟩, -556800), (⟨54, by omega⟩, -40960), (⟨70, by omega⟩, -40960), (⟨90, by omega⟩, -1113600)]
  nu := [(⟨0, by omega⟩, -556800), (⟨3, by omega⟩, 556800), (⟨4, by omega⟩, 556800), (⟨10, by omega⟩, -556800), (⟨11, by omega⟩, 556800), (⟨12, by omega⟩, 556800), (⟨15, by omega⟩, -556800), (⟨20, by omega⟩, -556800), (⟨21, by omega⟩, 556800), (⟨22, by omega⟩, 556800), (⟨24, by omega⟩, 40960), (⟨25, by omega⟩, -556800), (⟨27, by omega⟩, -40960), (⟨29, by omega⟩, -40960), (⟨30, by omega⟩, -556800), (⟨33, by omega⟩, 556800), (⟨34, by omega⟩, 556800), (⟨40, by omega⟩, -556800)]
  claimed := 90680815042560000
}
def branch_box_1334 : RatBox 8 := { lower := box_1334.profileLo, upper := box_1334.profileHi }
def accepted_1334 : Bool := checkAt 527 1000 box_1334 cert_1334

def box_1338 : Box := { S := 10995200, lo := ![0, 7305795, 0, 8912125, 10857760, 0, 10720320, 0], hi := ![274880, 7353040, 549760, 8959370, 10995200, 137440, 10995200, 274880] }
def cert_1338 : Certificate := {
  mu := [(⟨4, by omega⟩, -274880), (⟨6, by omega⟩, -10995200), (⟨13, by omega⟩, -10995200), (⟨34, by omega⟩, -10995200), (⟨54, by omega⟩, -819200), (⟨70, by omega⟩, -819200), (⟨90, by omega⟩, -21990400)]
  nu := [(⟨0, by omega⟩, -10995200), (⟨3, by omega⟩, 10995200), (⟨4, by omega⟩, 10995200), (⟨10, by omega⟩, -10995200), (⟨11, by omega⟩, 10995200), (⟨12, by omega⟩, 10995200), (⟨15, by omega⟩, -10995200), (⟨20, by omega⟩, -10995200), (⟨21, by omega⟩, 10995200), (⟨22, by omega⟩, 10995200), (⟨24, by omega⟩, 819200), (⟨25, by omega⟩, -10995200), (⟨27, by omega⟩, -819200), (⟨29, by omega⟩, -819200), (⟨30, by omega⟩, -10995200), (⟨33, by omega⟩, 10995200), (⟨34, by omega⟩, 10995200), (⟨40, by omega⟩, -10995200)]
  claimed := 698276032347504640000
}
def branch_box_1338 : RatBox 8 := { lower := box_1338.profileLo, upper := box_1338.profileHi }
def accepted_1338 : Bool := checkAt 527 1000 box_1338 cert_1338

def box_1342 : Box := { S := 145369600, lo := ![3634240, 92218840, 0, 117204240, 138101120, 3634240, 138101120, 0], hi := ![7268480, 97215920, 3634240, 122201320, 145369600, 7268480, 145369600, 7268480] }
def cert_1342 : Certificate := {
  mu := [(⟨4, by omega⟩, -32791800), (⟨5, by omega⟩, -77670400), (⟨6, by omega⟩, -67699200), (⟨10, by omega⟩, -77670400), (⟨13, by omega⟩, -67699200), (⟨21, by omega⟩, -67699200), (⟨30, by omega⟩, -67699200), (⟨33, by omega⟩, -7577600), (⟨37, by omega⟩, -77670400), (⟨42, by omega⟩, -77670400), (⟨45, by omega⟩, -67699200), (⟨54, by omega⟩, -67699200), (⟨61, by omega⟩, -7577600), (⟨70, by omega⟩, -7577600), (⟨74, by omega⟩, -77670400), (⟨78, by omega⟩, -67699200), (⟨86, by omega⟩, -67699200), (⟨89, by omega⟩, -28634400), (⟨90, by omega⟩, -45756000), (⟨94, by omega⟩, -135398400)]
  nu := [(⟨0, by omega⟩, -67699200), (⟨3, by omega⟩, 37195200), (⟨4, by omega⟩, 67699200), (⟨5, by omega⟩, -77670400), (⟨10, by omega⟩, -67699200), (⟨11, by omega⟩, 67699200), (⟨12, by omega⟩, 67699200), (⟨13, by omega⟩, 67699200), (⟨14, by omega⟩, 67699200), (⟨15, by omega⟩, -67699200), (⟨16, by omega⟩, -67699200), (⟨17, by omega⟩, -67699200), (⟨18, by omega⟩, -67699200), (⟨19, by omega⟩, -67699200), (⟨20, by omega⟩, -67699200), (⟨21, by omega⟩, 67699200), (⟨22, by omega⟩, 7577600), (⟨23, by omega⟩, 67699200), (⟨24, by omega⟩, 67699200), (⟨25, by omega⟩, -7577600), (⟨26, by omega⟩, -67699200), (⟨27, by omega⟩, -67699200), (⟨28, by omega⟩, -7577600), (⟨29, by omega⟩, -7577600), (⟨30, by omega⟩, -114865600), (⟨31, by omega⟩, 77670400), (⟨32, by omega⟩, 77670400), (⟨33, by omega⟩, 114865600), (⟨34, by omega⟩, 37195200), (⟨35, by omega⟩, -77670400), (⟨36, by omega⟩, -77670400), (⟨38, by omega⟩, -77670400), (⟨40, by omega⟩, -37195200), (⟨41, by omega⟩, -67699200)]
  claimed := 1596394394215770193920000
}
def branch_box_1342 : RatBox 8 := { lower := box_1342.profileLo, upper := box_1342.profileHi }
def accepted_1342 : Bool := checkAt 527 1000 box_1342 cert_1342

def box_1344 : Box := { S := 111317808000, lo := ![2782945200, 70617234450, 0, 89749982700, 105751917600, 0, 105751917600, 2782945200], hi := ![5565890400, 74443784100, 2782945200, 93576532350, 111317808000, 2782945200, 111317808000, 5565890400] }
def cert_1344 : Certificate := {
  mu := [(⟨5, by omega⟩, -60931852800), (⟨6, by omega⟩, -50385955200), (⟨10, by omega⟩, -60931852800), (⟨13, by omega⟩, -50385955200), (⟨22, by omega⟩, -5526748800), (⟨30, by omega⟩, -50385955200), (⟨33, by omega⟩, -4974028800), (⟨37, by omega⟩, -60931852800), (⟨42, by omega⟩, -11435110400), (⟨45, by omega⟩, -5019148800), (⟨53, by omega⟩, -50385955200), (⟨61, by omega⟩, -50938675200), (⟨69, by omega⟩, -4974028800), (⟨74, by omega⟩, -11435110400), (⟨86, by omega⟩, -50385955200), (⟨89, by omega⟩, -100771910400), (⟨93, by omega⟩, -10038297600)]
  nu := [(⟨0, by omega⟩, -50385955200), (⟨3, by omega⟩, 50385955200), (⟨4, by omega⟩, 50385955200), (⟨5, by omega⟩, -60931852800), (⟨10, by omega⟩, -50385955200), (⟨11, by omega⟩, 50385955200), (⟨12, by omega⟩, 50385955200), (⟨14, by omega⟩, 50385955200), (⟨15, by omega⟩, -50385955200), (⟨16, by omega⟩, -5526748800), (⟨17, by omega⟩, -50385955200), (⟨19, by omega⟩, -50385955200), (⟨20, by omega⟩, -50385955200), (⟨21, by omega⟩, 50385955200), (⟨22, by omega⟩, 4974028800), (⟨23, by omega⟩, 5019148800), (⟨24, by omega⟩, 50385955200), (⟨25, by omega⟩, -4974028800), (⟨26, by omega⟩, -5019148800), (⟨27, by omega⟩, -50385955200), (⟨28, by omega⟩, -50938675200), (⟨29, by omega⟩, -4974028800), (⟨30, by omega⟩, -61821065600), (⟨31, by omega⟩, 11435110400), (⟨32, by omega⟩, 11435110400), (⟨33, by omega⟩, 61821065600), (⟨34, by omega⟩, 50385955200), (⟨35, by omega⟩, -60931852800), (⟨36, by omega⟩, -11435110400), (⟨38, by omega⟩, -11435110400), (⟨40, by omega⟩, -50385955200), (⟨41, by omega⟩, -5019148800)]
  claimed := 724068682944925785209535744000000
}
def branch_box_1344 : RatBox 8 := { lower := box_1344.profileLo, upper := box_1344.profileHi }
def accepted_1344 : Bool := checkAt 527 1000 box_1344 cert_1344

def box_1345 : Box := { S := 2726150400, lo := ![68153760, 1729401660, 0, 2197958760, 2589842880, 0, 2589842880, 0], hi := ![136307520, 1823113080, 68153760, 2291670180, 2657996640, 68153760, 2726150400, 68153760] }
def cert_1345 : Certificate := {
  mu := [(⟨5, by omega⟩, -1530470400), (⟨6, by omega⟩, -1195680000), (⟨10, by omega⟩, -1530470400), (⟨13, by omega⟩, -1195680000), (⟨22, by omega⟩, -1530470400), (⟨33, by omega⟩, -231014400), (⟨37, by omega⟩, -1530470400), (⟨42, by omega⟩, -1530470400), (⟨45, by omega⟩, -115507200), (⟨50, by omega⟩, -135680000), (⟨62, by omega⟩, -1530470400), (⟨74, by omega⟩, -1530470400), (⟨82, by omega⟩, -135680000), (⟨89, by omega⟩, -2391360000)]
  nu := [(⟨0, by omega⟩, -1195680000), (⟨3, by omega⟩, 1195680000), (⟨4, by omega⟩, 1195680000), (⟨5, by omega⟩, -1530470400), (⟨10, by omega⟩, -1195680000), (⟨11, by omega⟩, 1195680000), (⟨12, by omega⟩, 1195680000), (⟨15, by omega⟩, -1195680000), (⟨16, by omega⟩, -1530470400), (⟨20, by omega⟩, -1195680000), (⟨21, by omega⟩, 1195680000), (⟨22, by omega⟩, 231014400), (⟨23, by omega⟩, 115507200), (⟨25, by omega⟩, -231014400), (⟨26, by omega⟩, -115507200), (⟨28, by omega⟩, -1530470400), (⟨30, by omega⟩, -2861830400), (⟨31, by omega⟩, 1666150400), (⟨32, by omega⟩, 1666150400), (⟨33, by omega⟩, 2726150400), (⟨34, by omega⟩, 1331360000), (⟨35, by omega⟩, -1530470400), (⟨36, by omega⟩, -1530470400), (⟨37, by omega⟩, -135680000), (⟨38, by omega⟩, -1530470400), (⟨39, by omega⟩, -135680000), (⟨40, by omega⟩, -1195680000)]
  claimed := 10619916604476623706562560000
}
def branch_box_1345 : RatBox 8 := { lower := box_1345.profileLo, upper := box_1345.profileHi }
def accepted_1345 : Bool := checkAt 527 1000 box_1345 cert_1345

def box_1347 : Box := { S := 17875200, lo := ![446880, 11339580, 0, 14411880, 17428320, 0, 16981440, 0], hi := ![893760, 11954040, 446880, 15026340, 17875200, 446880, 17428320, 446880] }
def cert_1347 : Certificate := {
  mu := [(⟨4, by omega⟩, -4189500), (⟨5, by omega⟩, -10035200), (⟨6, by omega⟩, -7840000), (⟨10, by omega⟩, -10035200), (⟨13, by omega⟩, -7840000), (⟨22, by omega⟩, -2195200), (⟨30, by omega⟩, -7840000), (⟨33, by omega⟩, -819200), (⟨37, by omega⟩, -10035200), (⟨41, by omega⟩, -7840000), (⟨42, by omega⟩, -2195200), (⟨50, by omega⟩, -10035200), (⟨54, by omega⟩, -7840000), (⟨61, by omega⟩, -9216000), (⟨70, by omega⟩, -819200), (⟨74, by omega⟩, -10035200), (⟨82, by omega⟩, -10035200), (⟨86, by omega⟩, -7840000), (⟨90, by omega⟩, -20070400)]
  nu := [(⟨0, by omega⟩, -10035200), (⟨3, by omega⟩, 10035200), (⟨4, by omega⟩, 10035200), (⟨5, by omega⟩, -10035200), (⟨10, by omega⟩, -7840000), (⟨11, by omega⟩, 7840000), (⟨12, by omega⟩, 7840000), (⟨14, by omega⟩, 7840000), (⟨15, by omega⟩, -7840000), (⟨16, by omega⟩, -2195200), (⟨17, by omega⟩, -7840000), (⟨19, by omega⟩, -7840000), (⟨20, by omega⟩, -7840000), (⟨21, by omega⟩, 7840000), (⟨22, by omega⟩, 819200), (⟨24, by omega⟩, 7840000), (⟨25, by omega⟩, -819200), (⟨27, by omega⟩, -7840000), (⟨28, by omega⟩, -9216000), (⟨29, by omega⟩, -819200), (⟨30, by omega⟩, -30105600), (⟨31, by omega⟩, 20070400), (⟨32, by omega⟩, 20070400), (⟨33, by omega⟩, 20070400), (⟨34, by omega⟩, 20070400), (⟨35, by omega⟩, -10035200), (⟨36, by omega⟩, -10035200), (⟨37, by omega⟩, -10035200), (⟨38, by omega⟩, -10035200), (⟨39, by omega⟩, -10035200), (⟨40, by omega⟩, -10035200)]
  claimed := 2962497905312440320000
}
def branch_box_1347 : RatBox 8 := { lower := box_1347.profileLo, upper := box_1347.profileHi }
def accepted_1347 : Bool := checkAt 527 1000 box_1347 cert_1347

end PeaceableQueens.UpperBound.Generated.Even.Core
