import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Sound
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

def box_2554 : Box := { S := 2560, lo := ![0, 1855, 0, 1921, 2480, 0, 2544, 0], hi := ![64, 1866, 128, 1932, 2496, 32, 2560, 64] }
def cert_2554 : Certificate := {
  mu := [(⟨6, by omega⟩, -2560), (⟨89, by omega⟩, -5120)]
  nu := [(⟨0, by omega⟩, -2560), (⟨3, by omega⟩, 2560), (⟨4, by omega⟩, 2560), (⟨10, by omega⟩, -2560), (⟨12, by omega⟩, 2560), (⟨20, by omega⟩, -2560), (⟨21, by omega⟩, 2560), (⟨30, by omega⟩, -2560), (⟨33, by omega⟩, 2560), (⟨34, by omega⟩, 2560), (⟨40, by omega⟩, -2560)]
  claimed := 8814592000
}
def branch_box_2554 : RatBox 8 := { lower := box_2554.profileLo, upper := box_2554.profileHi }
def accepted_2554 : Bool := checkAt 527 1000 box_2554 cert_2554

def box_2556 : Box := { S := 11370496000, lo := ![0, 8288025600, 0, 8483456000, 10944102400, 0, 11228364800, 0], hi := ![284262400, 8385740800, 568524800, 8581171200, 11086233600, 142131200, 11370496000, 284262400] }
def cert_2556 : Certificate := {
  mu := [(⟨5, by omega⟩, -568524800), (⟨6, by omega⟩, -10801971200), (⟨9, by omega⟩, -568524800), (⟨21, by omega⟩, -568524800), (⟨34, by omega⟩, -78643200), (⟨37, by omega⟩, -568524800), (⟨42, by omega⟩, -568524800), (⟨46, by omega⟩, -52428800), (⟨50, by omega⟩, -568524800), (⟨62, by omega⟩, -568524800), (⟨74, by omega⟩, -568524800), (⟨82, by omega⟩, -568524800), (⟨89, by omega⟩, -21603942400)]
  nu := [(⟨0, by omega⟩, -10801971200), (⟨3, by omega⟩, 10801971200), (⟨4, by omega⟩, 10801971200), (⟨5, by omega⟩, -568524800), (⟨10, by omega⟩, -10801971200), (⟨12, by omega⟩, 10801971200), (⟨16, by omega⟩, -568524800), (⟨20, by omega⟩, -10801971200), (⟨21, by omega⟩, 10801971200), (⟨22, by omega⟩, 78643200), (⟨23, by omega⟩, 52428800), (⟨25, by omega⟩, -78643200), (⟨26, by omega⟩, -52428800), (⟨28, by omega⟩, -568524800), (⟨30, by omega⟩, -11939020800), (⟨31, by omega⟩, 1137049600), (⟨32, by omega⟩, 1137049600), (⟨33, by omega⟩, 11370496000), (⟨34, by omega⟩, 11370496000), (⟨35, by omega⟩, -568524800), (⟨36, by omega⟩, -568524800), (⟨37, by omega⟩, -568524800), (⟨38, by omega⟩, -568524800), (⟨39, by omega⟩, -568524800), (⟨40, by omega⟩, -10801971200)]
  claimed := 772734951408167240597504000000
}
def branch_box_2556 : RatBox 8 := { lower := box_2556.profileLo, upper := box_2556.profileHi }
def accepted_2556 : Bool := checkAt 527 1000 box_2556 cert_2556

def box_2559 : Box := { S := 456960, lo := ![0, 333081, 0, 337008, 439824, 0, 451248, 0], hi := ![11424, 337008, 22848, 340935, 442680, 5712, 454104, 11424] }
def cert_2559 : Certificate := {
  mu := [(⟨5, by omega⟩, -268800), (⟨6, by omega⟩, -188160), (⟨9, by omega⟩, -268800), (⟨21, by omega⟩, -268800), (⟨33, by omega⟩, -188160), (⟨37, by omega⟩, -268800), (⟨42, by omega⟩, -268800), (⟨45, by omega⟩, -25600), (⟨50, by omega⟩, -268800), (⟨62, by omega⟩, -268800), (⟨74, by omega⟩, -268800), (⟨82, by omega⟩, -268800), (⟨89, by omega⟩, -537600)]
  nu := [(⟨0, by omega⟩, -268800), (⟨3, by omega⟩, 268800), (⟨4, by omega⟩, 268800), (⟨5, by omega⟩, -268800), (⟨10, by omega⟩, -188160), (⟨12, by omega⟩, 188160), (⟨16, by omega⟩, -268800), (⟨20, by omega⟩, -188160), (⟨21, by omega⟩, 188160), (⟨22, by omega⟩, 188160), (⟨23, by omega⟩, 25600), (⟨25, by omega⟩, -188160), (⟨26, by omega⟩, -25600), (⟨28, by omega⟩, -268800), (⟨30, by omega⟩, -806400), (⟨31, by omega⟩, 537600), (⟨32, by omega⟩, 537600), (⟨33, by omega⟩, 537600), (⟨34, by omega⟩, 537600), (⟨35, by omega⟩, -268800), (⟨36, by omega⟩, -268800), (⟨37, by omega⟩, -268800), (⟨38, by omega⟩, -268800), (⟨39, by omega⟩, -268800), (⟨40, by omega⟩, -268800)]
  claimed := 50178256153804800
}
def branch_box_2559 : RatBox 8 := { lower := box_2559.profileLo, upper := box_2559.profileHi }
def accepted_2559 : Bool := checkAt 527 1000 box_2559 cert_2559

def box_2563 : Box := { S := 1832597624320, lo := ![0, 1335791862102, 0, 1351540747936, 1763875213408, 0, 1821143889168, 0], hi := ![45814940608, 1343666305019, 91629881216, 1367289633770, 1769602080984, 22907470304, 1832597624320, 45814940608] }
def cert_2563 : Certificate := {
  mu := [(⟨5, by omega⟩, -1078742220800), (⟨6, by omega⟩, -753855403520), (⟨9, by omega⟩, -1078742220800), (⟨21, by omega⟩, -1078742220800), (⟨33, by omega⟩, -151624089600), (⟨37, by omega⟩, -1078742220800), (⟨41, by omega⟩, -1078742220800), (⟨45, by omega⟩, -101082726400), (⟨49, by omega⟩, -110106681344), (⟨62, by omega⟩, -1078742220800), (⟨74, by omega⟩, -1078742220800), (⟨82, by omega⟩, -110106681344), (⟨89, by omega⟩, -1507710807040)]
  nu := [(⟨0, by omega⟩, -753855403520), (⟨3, by omega⟩, 753855403520), (⟨4, by omega⟩, 753855403520), (⟨5, by omega⟩, -1078742220800), (⟨10, by omega⟩, -753855403520), (⟨12, by omega⟩, 753855403520), (⟨16, by omega⟩, -1078742220800), (⟨20, by omega⟩, -753855403520), (⟨21, by omega⟩, 753855403520), (⟨22, by omega⟩, 151624089600), (⟨23, by omega⟩, 101082726400), (⟨25, by omega⟩, -151624089600), (⟨26, by omega⟩, -101082726400), (⟨28, by omega⟩, -1078742220800), (⟨30, by omega⟩, -1942704305664), (⟨31, by omega⟩, 1188848902144), (⟨32, by omega⟩, 1188848902144), (⟨33, by omega⟩, 1832597624320), (⟨34, by omega⟩, 863962084864), (⟨35, by omega⟩, -1078742220800), (⟨36, by omega⟩, -1078742220800), (⟨37, by omega⟩, -110106681344), (⟨38, by omega⟩, -1078742220800), (⟨39, by omega⟩, -110106681344), (⟨40, by omega⟩, -753855403520)]
  claimed := 3240449651906591988711119455761203200
}
def branch_box_2563 : RatBox 8 := { lower := box_2563.profileLo, upper := box_2563.profileHi }
def accepted_2563 : Bool := checkAt 527 1000 box_2563 cert_2563

def box_2565 : Box := { S := 7604139520, lo := ![0, 5542704822, 0, 5608052896, 7342747224, 0, 7556613648, 0], hi := ![190103488, 5575378859, 380206976, 5673400970, 7366510160, 95051744, 7580376584, 190103488] }
def cert_2565 : Certificate := {
  mu := [(⟨5, by omega⟩, -4476108800), (⟨6, by omega⟩, -3128030720), (⟨9, by omega⟩, -4476108800), (⟨21, by omega⟩, -4476108800), (⟨33, by omega⟩, -629145600), (⟨37, by omega⟩, -4476108800), (⟨41, by omega⟩, -4476108800), (⟨45, by omega⟩, -419430400), (⟨49, by omega⟩, -1678540800), (⟨50, by omega⟩, -2797568000), (⟨62, by omega⟩, -4476108800), (⟨74, by omega⟩, -4476108800), (⟨82, by omega⟩, -4476108800), (⟨89, by omega⟩, -8952217600)]
  nu := [(⟨0, by omega⟩, -4476108800), (⟨3, by omega⟩, 4476108800), (⟨4, by omega⟩, 4476108800), (⟨5, by omega⟩, -4476108800), (⟨10, by omega⟩, -3128030720), (⟨12, by omega⟩, 3128030720), (⟨16, by omega⟩, -4476108800), (⟨20, by omega⟩, -3128030720), (⟨21, by omega⟩, 3128030720), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -4476108800), (⟨30, by omega⟩, -13428326400), (⟨31, by omega⟩, 8952217600), (⟨32, by omega⟩, 8952217600), (⟨33, by omega⟩, 8952217600), (⟨34, by omega⟩, 8952217600), (⟨35, by omega⟩, -4476108800), (⟨36, by omega⟩, -4476108800), (⟨37, by omega⟩, -4476108800), (⟨38, by omega⟩, -4476108800), (⟨39, by omega⟩, -4476108800), (⟨40, by omega⟩, -4476108800)]
  claimed := 231552232880581459955921715200
}
def branch_box_2565 : RatBox 8 := { lower := box_2565.profileLo, upper := box_2565.profileHi }
def accepted_2565 : Bool := checkAt 527 1000 box_2565 cert_2565

def box_2568 : Box := { S := 174568243200, lo := ![0, 127993981440, 0, 129494177280, 168021934080, 0, 173477191680, 0], hi := ![4364206080, 128744079360, 8728412160, 130244275200, 169112985600, 2182103040, 174568243200, 4364206080] }
def cert_2568 : Certificate := {
  mu := [(⟨5, by omega⟩, -4476108800), (⟨6, by omega⟩, -170092134400), (⟨9, by omega⟩, -4476108800), (⟨21, by omega⟩, -4476108800), (⟨34, by omega⟩, -629145600), (⟨38, by omega⟩, -4476108800), (⟨42, by omega⟩, -4476108800), (⟨46, by omega⟩, -419430400), (⟨50, by omega⟩, -4476108800), (⟨62, by omega⟩, -4476108800), (⟨74, by omega⟩, -4476108800), (⟨81, by omega⟩, -4476108800), (⟨89, by omega⟩, -340184268800)]
  nu := [(⟨0, by omega⟩, -170092134400), (⟨3, by omega⟩, 170092134400), (⟨4, by omega⟩, 170092134400), (⟨5, by omega⟩, -4476108800), (⟨10, by omega⟩, -170092134400), (⟨12, by omega⟩, 170092134400), (⟨16, by omega⟩, -4476108800), (⟨20, by omega⟩, -170092134400), (⟨21, by omega⟩, 170092134400), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -4476108800), (⟨30, by omega⟩, -179044352000), (⟨31, by omega⟩, 8952217600), (⟨32, by omega⟩, 8952217600), (⟨33, by omega⟩, 174568243200), (⟨34, by omega⟩, 174568243200), (⟨35, by omega⟩, -4476108800), (⟨36, by omega⟩, -4476108800), (⟨37, by omega⟩, -4476108800), (⟨38, by omega⟩, -4476108800), (⟨39, by omega⟩, -4476108800), (⟨40, by omega⟩, -170092134400)]
  claimed := 2795069134044584088723039191040000
}
def branch_box_2568 : RatBox 8 := { lower := box_2568.profileLo, upper := box_2568.profileHi }
def accepted_2568 : Bool := checkAt 527 1000 box_2568 cert_2568

def box_2569 : Box := { S := 7061107200, lo := ![0, 5177225865, 0, 5207566560, 6796315680, 0, 7016975280, 0], hi := ![176527680, 5207566560, 353055360, 5237907255, 6818381640, 88263840, 7061107200, 176527680] }
def cert_2569 : Certificate := {
  mu := [(⟨5, by omega⟩, -4145971200), (⟨6, by omega⟩, -2915136000), (⟨9, by omega⟩, -4145971200), (⟨21, by omega⟩, -4145971200), (⟨33, by omega⟩, -592281600), (⟨37, by omega⟩, -4145971200), (⟨42, by omega⟩, -4145971200), (⟨45, by omega⟩, -394854400), (⟨50, by omega⟩, -425779200), (⟨62, by omega⟩, -4145971200), (⟨74, by omega⟩, -4145971200), (⟨82, by omega⟩, -425779200), (⟨89, by omega⟩, -5830272000)]
  nu := [(⟨0, by omega⟩, -2915136000), (⟨3, by omega⟩, 2915136000), (⟨4, by omega⟩, 2915136000), (⟨5, by omega⟩, -4145971200), (⟨10, by omega⟩, -2915136000), (⟨12, by omega⟩, 2915136000), (⟨16, by omega⟩, -4145971200), (⟨20, by omega⟩, -2915136000), (⟨21, by omega⟩, 2915136000), (⟨22, by omega⟩, 592281600), (⟨23, by omega⟩, 394854400), (⟨25, by omega⟩, -592281600), (⟨26, by omega⟩, -394854400), (⟨28, by omega⟩, -4145971200), (⟨30, by omega⟩, -7486886400), (⟨31, by omega⟩, 4571750400), (⟨32, by omega⟩, 4571750400), (⟨33, by omega⟩, 7061107200), (⟨34, by omega⟩, 3340915200), (⟨35, by omega⟩, -4145971200), (⟨36, by omega⟩, -4145971200), (⟨37, by omega⟩, -425779200), (⟨38, by omega⟩, -4145971200), (⟨39, by omega⟩, -425779200), (⟨40, by omega⟩, -2915136000)]
  claimed := 185365173280827493664686080000
}
def branch_box_2569 : RatBox 8 := { lower := box_2569.profileLo, upper := box_2569.profileHi }
def accepted_2569 : Bool := checkAt 527 1000 box_2569 cert_2569

def box_2571 : Box := { S := 29299200, lo := ![0, 21482265, 0, 21608160, 28292040, 0, 29116080, 0], hi := ![732480, 21608160, 1464960, 21734055, 28383600, 366240, 29207640, 732480] }
def cert_2571 : Certificate := {
  mu := [(⟨5, by omega⟩, -17203200), (⟨6, by omega⟩, -12096000), (⟨9, by omega⟩, -17203200), (⟨21, by omega⟩, -17203200), (⟨33, by omega⟩, -2457600), (⟨37, by omega⟩, -17203200), (⟨42, by omega⟩, -17203200), (⟨45, by omega⟩, -1638400), (⟨50, by omega⟩, -17203200), (⟨62, by omega⟩, -17203200), (⟨74, by omega⟩, -17203200), (⟨82, by omega⟩, -17203200), (⟨89, by omega⟩, -34406400)]
  nu := [(⟨0, by omega⟩, -17203200), (⟨3, by omega⟩, 17203200), (⟨4, by omega⟩, 17203200), (⟨5, by omega⟩, -17203200), (⟨10, by omega⟩, -12096000), (⟨12, by omega⟩, 12096000), (⟨16, by omega⟩, -17203200), (⟨20, by omega⟩, -12096000), (⟨21, by omega⟩, 12096000), (⟨22, by omega⟩, 2457600), (⟨23, by omega⟩, 1638400), (⟨25, by omega⟩, -2457600), (⟨26, by omega⟩, -1638400), (⟨28, by omega⟩, -17203200), (⟨30, by omega⟩, -51609600), (⟨31, by omega⟩, 34406400), (⟨32, by omega⟩, 34406400), (⟨33, by omega⟩, 34406400), (⟨34, by omega⟩, 34406400), (⟨35, by omega⟩, -17203200), (⟨36, by omega⟩, -17203200), (⟨37, by omega⟩, -17203200), (⟨38, by omega⟩, -17203200), (⟨39, by omega⟩, -17203200), (⟨40, by omega⟩, -17203200)]
  claimed := 13245598795306106880000
}
def branch_box_2571 : RatBox 8 := { lower := box_2571.profileLo, upper := box_2571.profileHi }
def accepted_2571 : Bool := checkAt 527 1000 box_2571 cert_2571

def box_2577 : Box := { S := 7604139520, lo := ![0, 5542704822, 0, 5608052896, 7366510160, 0, 7509087776, 0], hi := ![190103488, 5575378859, 380206976, 5673400970, 7390273096, 95051744, 7556613648, 190103488] }
def cert_2577 : Certificate := {
  mu := [(⟨5, by omega⟩, -4476108800), (⟨6, by omega⟩, -3128030720), (⟨9, by omega⟩, -4476108800), (⟨21, by omega⟩, -4476108800), (⟨33, by omega⟩, -629145600), (⟨37, by omega⟩, -4476108800), (⟨41, by omega⟩, -4476108800), (⟨49, by omega⟩, -839270400), (⟨50, by omega⟩, -3636838400), (⟨62, by omega⟩, -4476108800), (⟨74, by omega⟩, -4476108800), (⟨77, by omega⟩, -3128030720), (⟨82, by omega⟩, -4476108800), (⟨89, by omega⟩, -8952217600)]
  nu := [(⟨0, by omega⟩, -4476108800), (⟨3, by omega⟩, 4476108800), (⟨4, by omega⟩, 4476108800), (⟨5, by omega⟩, -4476108800), (⟨10, by omega⟩, -3128030720), (⟨12, by omega⟩, 3128030720), (⟨13, by omega⟩, 3128030720), (⟨16, by omega⟩, -4476108800), (⟨18, by omega⟩, -3128030720), (⟨20, by omega⟩, -3128030720), (⟨21, by omega⟩, 3128030720), (⟨22, by omega⟩, 629145600), (⟨25, by omega⟩, -629145600), (⟨28, by omega⟩, -4476108800), (⟨30, by omega⟩, -13428326400), (⟨31, by omega⟩, 8952217600), (⟨32, by omega⟩, 8952217600), (⟨33, by omega⟩, 8952217600), (⟨34, by omega⟩, 8952217600), (⟨35, by omega⟩, -4476108800), (⟨36, by omega⟩, -4476108800), (⟨37, by omega⟩, -4476108800), (⟨38, by omega⟩, -4476108800), (⟨39, by omega⟩, -4476108800), (⟨40, by omega⟩, -4476108800)]
  claimed := 231592673780722991544696832000
}
def branch_box_2577 : RatBox 8 := { lower := box_2577.profileLo, upper := box_2577.profileHi }
def accepted_2577 : Bool := checkAt 527 1000 box_2577 cert_2577

def box_2579 : Box := { S := 7604139520, lo := ![0, 5542704822, 0, 5608052896, 7390273096, 0, 7509087776, 0], hi := ![190103488, 5575378859, 380206976, 5673400970, 7414036032, 95051744, 7532850712, 190103488] }
def cert_2579 : Certificate := {
  mu := [(⟨5, by omega⟩, -4476108800), (⟨6, by omega⟩, -3128030720), (⟨9, by omega⟩, -4476108800), (⟨21, by omega⟩, -4476108800), (⟨33, by omega⟩, -629145600), (⟨37, by omega⟩, -4476108800), (⟨41, by omega⟩, -4476108800), (⟨49, by omega⟩, -1678540800), (⟨50, by omega⟩, -2797568000), (⟨62, by omega⟩, -4476108800), (⟨74, by omega⟩, -4476108800), (⟨77, by omega⟩, -3128030720), (⟨82, by omega⟩, -4476108800), (⟨90, by omega⟩, -8952217600)]
  nu := [(⟨0, by omega⟩, -4476108800), (⟨3, by omega⟩, 4476108800), (⟨4, by omega⟩, 4476108800), (⟨5, by omega⟩, -4476108800), (⟨10, by omega⟩, -3128030720), (⟨12, by omega⟩, 3128030720), (⟨13, by omega⟩, 3128030720), (⟨16, by omega⟩, -4476108800), (⟨18, by omega⟩, -3128030720), (⟨20, by omega⟩, -3128030720), (⟨21, by omega⟩, 3128030720), (⟨22, by omega⟩, 629145600), (⟨25, by omega⟩, -629145600), (⟨28, by omega⟩, -4476108800), (⟨30, by omega⟩, -13428326400), (⟨31, by omega⟩, 8952217600), (⟨32, by omega⟩, 8952217600), (⟨33, by omega⟩, 8952217600), (⟨34, by omega⟩, 8952217600), (⟨35, by omega⟩, -4476108800), (⟨36, by omega⟩, -4476108800), (⟨37, by omega⟩, -4476108800), (⟨38, by omega⟩, -4476108800), (⟨39, by omega⟩, -4476108800), (⟨40, by omega⟩, -4476108800)]
  claimed := 231623004455829140236278169600
}
def branch_box_2579 : RatBox 8 := { lower := box_2579.profileLo, upper := box_2579.profileHi }
def accepted_2579 : Bool := checkAt 527 1000 box_2579 cert_2579

def box_2582 : Box := { S := 89522176000, lo := ![0, 65637939200, 0, 66407270400, 86724608000, 0, 88403148800, 0], hi := ![2238054400, 66022604800, 4476108800, 66791936000, 87284121600, 1119027200, 88962662400, 2238054400] }
def cert_2582 : Certificate := {
  mu := [(⟨5, by omega⟩, -4476108800), (⟨6, by omega⟩, -85046067200), (⟨9, by omega⟩, -4476108800), (⟨21, by omega⟩, -4476108800), (⟨34, by omega⟩, -629145600), (⟨38, by omega⟩, -4476108800), (⟨42, by omega⟩, -4476108800), (⟨46, by omega⟩, -419430400), (⟨49, by omega⟩, -4476108800), (⟨62, by omega⟩, -4476108800), (⟨74, by omega⟩, -4476108800), (⟨82, by omega⟩, -4476108800), (⟨89, by omega⟩, -170092134400)]
  nu := [(⟨0, by omega⟩, -85046067200), (⟨3, by omega⟩, 85046067200), (⟨4, by omega⟩, 85046067200), (⟨5, by omega⟩, -4476108800), (⟨10, by omega⟩, -85046067200), (⟨12, by omega⟩, 85046067200), (⟨16, by omega⟩, -4476108800), (⟨20, by omega⟩, -85046067200), (⟨21, by omega⟩, 85046067200), (⟨22, by omega⟩, 629145600), (⟨23, by omega⟩, 419430400), (⟨25, by omega⟩, -629145600), (⟨26, by omega⟩, -419430400), (⟨28, by omega⟩, -4476108800), (⟨30, by omega⟩, -93998284800), (⟨31, by omega⟩, 8952217600), (⟨32, by omega⟩, 8952217600), (⟨33, by omega⟩, 89522176000), (⟨34, by omega⟩, 89522176000), (⟨35, by omega⟩, -4476108800), (⟨36, by omega⟩, -4476108800), (⟨37, by omega⟩, -4476108800), (⟨38, by omega⟩, -4476108800), (⟨39, by omega⟩, -4476108800), (⟨40, by omega⟩, -85046067200)]
  claimed := 377126026239329043866451968000000
}
def branch_box_2582 : RatBox 8 := { lower := box_2582.profileLo, upper := box_2582.profileHi }
def accepted_2582 : Bool := checkAt 527 1000 box_2582 cert_2582

def box_2583 : Box := { S := 279040, lo := ![0, 204593, 0, 205792, 270320, 0, 275552, 0], hi := ![6976, 205792, 13952, 206991, 271192, 3488, 277296, 6976] }
def cert_2583 : Certificate := {
  mu := [(⟨5, by omega⟩, -163840), (⟨6, by omega⟩, -115200), (⟨9, by omega⟩, -163840), (⟨21, by omega⟩, -163840), (⟨33, by omega⟩, -115200), (⟨37, by omega⟩, -163840), (⟨42, by omega⟩, -163840), (⟨45, by omega⟩, -115200), (⟨50, by omega⟩, -163840), (⟨62, by omega⟩, -163840), (⟨74, by omega⟩, -163840), (⟨77, by omega⟩, -115200), (⟨82, by omega⟩, -163840), (⟨89, by omega⟩, -327680)]
  nu := [(⟨0, by omega⟩, -163840), (⟨3, by omega⟩, 163840), (⟨4, by omega⟩, 163840), (⟨5, by omega⟩, -163840), (⟨10, by omega⟩, -115200), (⟨12, by omega⟩, 115200), (⟨13, by omega⟩, 115200), (⟨16, by omega⟩, -163840), (⟨18, by omega⟩, -115200), (⟨20, by omega⟩, -115200), (⟨21, by omega⟩, 115200), (⟨22, by omega⟩, 115200), (⟨23, by omega⟩, 115200), (⟨25, by omega⟩, -115200), (⟨26, by omega⟩, -115200), (⟨28, by omega⟩, -163840), (⟨30, by omega⟩, -491520), (⟨31, by omega⟩, 327680), (⟨32, by omega⟩, 327680), (⟨33, by omega⟩, 327680), (⟨34, by omega⟩, 327680), (⟨35, by omega⟩, -163840), (⟨36, by omega⟩, -163840), (⟨37, by omega⟩, -163840), (⟨38, by omega⟩, -163840), (⟨39, by omega⟩, -163840), (⟨40, by omega⟩, -163840)]
  claimed := 11444039555481600
}
def branch_box_2583 : RatBox 8 := { lower := box_2583.profileLo, upper := box_2583.profileHi }
def accepted_2583 : Bool := checkAt 527 1000 box_2583 cert_2583

def box_2585 : Box := { S := 1395200, lo := ![0, 1022965, 0, 1028960, 1355960, 0, 1377760, 0], hi := ![34880, 1028960, 69760, 1034955, 1360320, 17440, 1382120, 34880] }
def cert_2585 : Certificate := {
  mu := [(⟨5, by omega⟩, -819200), (⟨6, by omega⟩, -576000), (⟨9, by omega⟩, -819200), (⟨21, by omega⟩, -819200), (⟨33, by omega⟩, -576000), (⟨37, by omega⟩, -819200), (⟨42, by omega⟩, -819200), (⟨45, by omega⟩, -576000), (⟨50, by omega⟩, -819200), (⟨62, by omega⟩, -819200), (⟨74, by omega⟩, -819200), (⟨77, by omega⟩, -576000), (⟨82, by omega⟩, -819200), (⟨90, by omega⟩, -1638400)]
  nu := [(⟨0, by omega⟩, -819200), (⟨3, by omega⟩, 819200), (⟨4, by omega⟩, 819200), (⟨5, by omega⟩, -819200), (⟨10, by omega⟩, -576000), (⟨12, by omega⟩, 576000), (⟨13, by omega⟩, 576000), (⟨16, by omega⟩, -819200), (⟨18, by omega⟩, -576000), (⟨20, by omega⟩, -576000), (⟨21, by omega⟩, 576000), (⟨22, by omega⟩, 576000), (⟨23, by omega⟩, 576000), (⟨25, by omega⟩, -576000), (⟨26, by omega⟩, -576000), (⟨28, by omega⟩, -819200), (⟨30, by omega⟩, -2457600), (⟨31, by omega⟩, 1638400), (⟨32, by omega⟩, 1638400), (⟨33, by omega⟩, 1638400), (⟨34, by omega⟩, 1638400), (⟨35, by omega⟩, -819200), (⟨36, by omega⟩, -819200), (⟨37, by omega⟩, -819200), (⟨38, by omega⟩, -819200), (⟨39, by omega⟩, -819200), (⟨40, by omega⟩, -819200)]
  claimed := 1430691816407040000
}
def branch_box_2585 : RatBox 8 := { lower := box_2585.profileLo, upper := box_2585.profileHi }
def accepted_2585 : Bool := checkAt 527 1000 box_2585 cert_2585

def box_2590 : Box := { S := 2560, lo := ![0, 1877, 0, 1899, 2480, 0, 2544, 0], hi := ![64, 1888, 128, 1910, 2496, 32, 2560, 64] }
def cert_2590 : Certificate := {
  mu := [(⟨6, by omega⟩, -2560), (⟨89, by omega⟩, -5120)]
  nu := [(⟨0, by omega⟩, -2560), (⟨3, by omega⟩, 2560), (⟨4, by omega⟩, 2560), (⟨10, by omega⟩, -2560), (⟨12, by omega⟩, 2560), (⟨20, by omega⟩, -2560), (⟨21, by omega⟩, 2560), (⟨30, by omega⟩, -2560), (⟨33, by omega⟩, 2560), (⟨34, by omega⟩, 2560), (⟨40, by omega⟩, -2560)]
  claimed := 8814592000
}
def branch_box_2590 : RatBox 8 := { lower := box_2590.profileLo, upper := box_2590.profileHi }
def accepted_2590 : Bool := checkAt 527 1000 box_2590 cert_2590

def box_2591 : Box := { S := 9571865600, lo := ![0, 6730218000, 0, 7059250880, 9332568960, 0, 9093272320, 0], hi := ![239296640, 7059250880, 478593280, 7388283760, 9571865600, 239296640, 9332568960, 239296640] }
def cert_2591 : Certificate := {
  mu := [(⟨4, by omega⟩, -2250645760), (⟨5, by omega⟩, -5548364800), (⟨6, by omega⟩, -4023500800), (⟨9, by omega⟩, -5548364800), (⟨21, by omega⟩, -1524864000), (⟨33, by omega⟩, -584038400), (⟨37, by omega⟩, -4667008000), (⟨38, by omega⟩, -881356800), (⟨41, by omega⟩, -2423731200), (⟨42, by omega⟩, -3124633600), (⟨45, by omega⟩, -4023500800), (⟨50, by omega⟩, -5548364800), (⟨54, by omega⟩, -4023500800), (⟨61, by omega⟩, -940825600), (⟨70, by omega⟩, -584038400), (⟨74, by omega⟩, -5548364800), (⟨82, by omega⟩, -5548364800), (⟨86, by omega⟩, -4023500800), (⟨90, by omega⟩, -11096729600), (⟨94, by omega⟩, -8047001600)]
  nu := [(⟨0, by omega⟩, -5548364800), (⟨3, by omega⟩, 5548364800), (⟨4, by omega⟩, 5548364800), (⟨5, by omega⟩, -5548364800), (⟨10, by omega⟩, -4023500800), (⟨12, by omega⟩, 4023500800), (⟨14, by omega⟩, 4023500800), (⟨16, by omega⟩, -1524864000), (⟨19, by omega⟩, -4023500800), (⟨20, by omega⟩, -4023500800), (⟨21, by omega⟩, 4023500800), (⟨22, by omega⟩, 584038400), (⟨23, by omega⟩, 4023500800), (⟨24, by omega⟩, 4023500800), (⟨25, by omega⟩, -584038400), (⟨26, by omega⟩, -4023500800), (⟨27, by omega⟩, -4023500800), (⟨28, by omega⟩, -940825600), (⟨29, by omega⟩, -584038400), (⟨30, by omega⟩, -16645094400), (⟨31, by omega⟩, 11096729600), (⟨32, by omega⟩, 11096729600), (⟨33, by omega⟩, 11096729600), (⟨34, by omega⟩, 11096729600), (⟨35, by omega⟩, -5548364800), (⟨36, by omega⟩, -5548364800), (⟨37, by omega⟩, -5548364800), (⟨38, by omega⟩, -5548364800), (⟨39, by omega⟩, -5548364800), (⟨40, by omega⟩, -5548364800), (⟨41, by omega⟩, -4023500800)]
  claimed := 459245965548946509384253440000
}
def branch_box_2591 : RatBox 8 := { lower := box_2591.profileLo, upper := box_2591.profileHi }
def accepted_2591 : Bool := checkAt 527 1000 box_2591 cert_2591

end PeaceableQueens.UpperBound.Generated.Even.Core
