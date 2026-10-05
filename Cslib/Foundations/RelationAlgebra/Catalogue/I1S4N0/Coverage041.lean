/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2625–2688 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage041

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            536870912
                            536870912)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            536870912
                            170141183460469231731687303716420976640)
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            140737488355328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9223372036854775808)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075632472132106952070080107642880
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            225971517691141795020824857073833476096
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            226854218932122817657624954171778138112
                            226854218932122817657624954171778138112)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            226854218932122817657624954171778138112
                            51933783384878441187866330991165440))
                        (Code.joinWords 256
                          39652766883359836930362572800
                          52085861687477613563370816300646400))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          43366073543301763436454086112043859968
                          218249502365998376621392460402130944)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            218077101883762874512981594178846720)
                          256)
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            14175143507624612150616770274723364864
                            51923602449334016627673845234401280))
                        (Code.joinWords 256
                          170805797458361689668139207246024278016
                          51923602410648390400005711643803648))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256))
                    1024))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          39614081257132168796771975168
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          39614081257132168796771975168
                          170141183460469231731687303715884105728)
                        256))
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            225971517691141795020824857073833476096
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            226854218932122817657624954171778138112
                            226854218932122817657624954171778138112)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            51923602410648390400005711643803648)
                          256)
                        (Nat.shiftLeft
                          2710379593980480136207619832204492800
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          55827738082243295884546660146639536128
                          256)
                        (Nat.shiftLeft
                          2710551994462111175406364121328779264
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            180775007426748558714917760198126862336)
                          (Code.joinWords 128
                            14175143458107010590730774324826865664
                            51923602410648390400005711643803648))
                        (Code.joinWords 256
                          39652766883359836930362572800
                          51923602410648390544120899719659520))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            51923602410648390400005711643803648)
                          256)
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            51923602410648390400005711643803648)
                          256)
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            51923602410648390400005711643803648)
                          256)
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            181439621424641016651369663728267067392
                            181481159799509295272397907698900795392)
                          (Code.joinWords 128
                            14175143458107010579201559278758395904
                            51923602410648390400005711643803648))
                        (Code.joinWords 256
                          181481159799509295272397907698900795392
                          51923602410648390400005711643803648))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        170143779608898499145501568964048715776
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        830767497365572420564879412675215360
                        (Nat.shiftLeft
                          2228224
                          128))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2475917857502623506959958016
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2475917857502623506959958016
                            128)
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          12089258196146291747061760
                          128)
                        (Nat.shiftLeft
                          584115552256
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          830767497365572420564879412675215360
                          128)
                        (Nat.shiftLeft
                          38280596832649216
                          128))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679724511123123931876961205060894720
                            225972207293068319177619271280377200640)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213510504684994698634735855584768163840
                            226854911227806867299406846558816174080)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            218779538772614342130085954842525696)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669695774073080370324659826619056128
                            40723275532331869523081590472704)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            10387287484266546801456206550401024)
                          256)
                        (Code.joinWords 256
                          562949953421312
                          40723275532331869523081590472704))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            834025399022240227258894736685006848
                            179999611379256110322340141518028800))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            3245185536584267267831560205762560)
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            2693757525484987478180494344200)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163914649369500429289355476992))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987619467738480640)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            10387287513280766472207306743349248)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            8589934592
                            128)
                          40723275532331869523081590472704))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51926296168173875387483892138115072
                            10387287522952173029124340140998656)
                          256)
                        (Code.joinWords 128
                          562949953421312
                          8589934592))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          140737488355328
                          140737488355328)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37383395344384
                            128)
                          256)
                        (Nat.shiftLeft
                          9481626453886709530624
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          12089258196146291747061760
                          128)
                        (Nat.shiftLeft
                          9481626453886709530624
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384752173394683785736179746340864
                          128)
                        256)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669695774073080370324659826619056128
                            43258576732788328326074996883456)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669695774073080370324659826619056128
                            40723275532331869523081590472704)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51964325686180722269528793234276352
                            158456325028528675187087900672)
                          256)
                        (Code.joinWords 256
                          41538374868278621028243970633760768
                          40723275532331869523081590472704))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494442496)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            158456325028528675187087900672)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51926296168173875387483892138115072
                            2693757525484996485379749052416)
                          256)
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51964325686180722269528793234276352
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            872305872233851041593123383308976128
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            51923760866973418928680898731704320
                            9007199254872064))
                        41538374868278621028243970633760768)
                      1024))))))
          65536))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        170143779608898499145501568964048715776
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        13292279957849158729038070602803445760
                        (Nat.shiftLeft
                          33685504
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      1024)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679724511123123931876961205060894720
                            225972207293068319177619271280377200640)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213510504684994698634735855584768163840
                            226854911227806867299406846558816174080)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335721101841984208764928)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2711234148941358991352903797252816896
                            40723275532331869523081590472704)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2417851639229258349412352
                            128)
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424))
                        (Nat.shiftLeft
                          10425316992601987128835874062598144
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335721101841984208764928)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            43258576732788328326074996883456)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335721101841984208764928)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374868278621028243970633760768
                            128)
                          (Code.joinWords 128
                            51926296168173875387483892138115072
                            2693757525484987478180494311424))
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          256))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            36029346774777856
                            36029346774777856)
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          2814749767106560
                          37926505815546838122496)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          13292279957849158729038070602803445760
                          2485551485127677583195897856)
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            146028888064
                            128)
                          151706023262187352489984)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2814749767106560
                          146028888064)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384752173394683785736179746340864
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            2596148429267413814265248164610048)
                          (Code.joinWords 128
                            13295727967481779522233513672376844288
                            689601926524156794414206543724544))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39652766883359836930362572800
                            3245185536584267267831560205762560)
                          (Code.joinWords 128
                            2672302063707149619773969837567508480
                            40723275532331869523081590505480)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          10425316992601987270699262324768768))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032))
                        (Code.joinWords 256
                          39652766883359836930362572800
                          (Code.joinWords 128
                            2669695774073080370327052913676910592
                            40723276174573711193353339535360)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2417851639229258349412352
                            128)
                          51964325686180722269528793234276352)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          10425316992601987272951062138454016))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            40723275532331869523081590603776
                            158456325028528675187087900672)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51926296168173875387483892138115072
                          2693757525484987478180494311424)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51964325686180722269528793234276352
                            158456325028528675187087900672)
                          256)
                        (Nat.shiftLeft
                          40723894502351512213219040034816
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            13333818332717437350066314573437206528
                            41538374868278621028243970633760768)
                          51923760866973418928680898731704320)
                        (Code.joinWords 256
                          13333818332717437350066314573437206528
                          618970019642690137449693184))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2228224
                            128)
                          256)
                        (Nat.shiftLeft
                          33685504
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469836194597111030471458816
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469836194597111030471458816
                          128)
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10384593717069655257060992658440192
                          10384593717069655257060992658440192)
                        256)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            851861203353370157805784554012672))
                        (Code.joinWords 256
                          2596148429267413814265248164610048
                          (Code.joinWords 128
                            661713613319135747581279073206272
                            43258576732788328326074996883456)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335721101841984208764928)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669695774073080370324659826619056128
                            40723275532331869523081590472704)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43258576732788328326074996883456
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            2758407706096627177656826174898176)
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335732631057030277234688))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494344200)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            166815213086433619860557161608249344
                            177241163904335732676269498167197696))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987654789549522944)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10427852293802443585387067655323648
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            137438953472)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472667473228983173120
                            128)
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525485034766698136207360))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            137438953472
                            128)
                          256))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687444453372461056
                            170141183460469231731687444453372461056)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            151706023299570747834368
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            158456325028528675187087900672
                            158456325028528675187087900672)
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256))
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            2535301200456458802993406410752)
                          (Code.joinWords 128
                            2669695823590681941739870822584025088
                            40723275532331869523081590505480)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10427852293802443585387067655323648
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            9444732965739290427392)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2659307852773185115965419905114701824
                            40564819207303340847894502572032))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669695826686325397522443610227736576
                            40723276335134171610921276801024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Code.joinWords 256
                          41538374868278621028806920587182080
                          (Code.joinWords 128
                            40726380101207878672088364482560
                            9444732965739290427392)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43258576732788328326074996883456
                            2693757525484987478180494442496)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            40723275532331869523081590603776
                            158456325028528675187087900672)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525484996522900583350272)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          (Nat.shiftLeft
                            9444733003260124725248
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            8589934592
                            128)
                          (Code.joinWords 128
                            40723894663502268441145682952192
                            161150756228064081870848)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            41538374868278621028243970633760768
                            41538374870696472667473228983173120)
                          (Nat.shiftLeft
                            9007336693825536
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            41538374868278621028806920587182080
                            36893488156009037824)
                          (Code.joinWords 128
                            618979464375655876740120576
                            9444732965876729380864)))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2624 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage041
