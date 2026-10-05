/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2433–2496 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage038

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255211775190703847611366013629108322304
                            309211662519466054948659636205300744192)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750316241357739813861654864987160576
                            311874874798140332085836371676270428160)
                          256)
                        512)))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750965327982658222589390371009069056
                            311708021566058379574974633973708226560)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            308384140257154668368507322343194886144
                            832075712978438448655374596333109248)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            308380895061714563784650464839241564160
                            3489223489090146671283166067598295040)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            308385600590646131288777846547434962944
                            830777638763804738865797473245331456)
                          256)
                        512)))))
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2876532459628294506205894966387933184
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2876533093492280246692379036405989376
                            128)
                          256)
                        512))
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297750965278465056651174179375044100096
                            128)
                          (Nat.shiftLeft
                            309090941617505120191884783358060789760
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222644505583631205186834268160
                            128)
                          (Nat.shiftLeft
                            3369313883513962458646597232582721536
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721538609735270400
                            128)
                          (Nat.shiftLeft
                            10846069241576739888958453983117049856
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2876532459628294506205894966387933184
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2876576193612688006492029924314972160
                            128)
                          256)
                        512))))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85901369368804990116855429262670299136
                            218087243088564700348193567804489728)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            830777638570374246400091386300858368
                            219385317303198407255326191886794752))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2876532459637965912762811999785582592))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            167461714892550016855320480242991104
                            218077101932119907297566761167093760)
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            55831632304887196996044685982031675392)
                          (Code.joinWords 128
                            85737964135987912934383884748619513856
                            710857891953839898327763102581391360))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85236745229707730349956627740477095936
                            219375176098396581420114218261151744)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231740910675752738881536
                            42535295865117307932921825928971026432)
                          (Code.joinWords 128
                            266510213154875632531048373641491251200
                            42742987739458701038063045782139830272))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85236745229707730354568313758904483840
                            218079637194634885102654210659319808)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            311043407555012166479273894751015796736)
                          (Code.joinWords 128
                            311706723468941212899446295992243060736
                            311749559937831165855947756985345114112))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42537892013546575346736091177135636480
                            2662512473491166542802210885405245440)
                          (Code.joinWords 128
                            669319517075247628900931826800918528
                            710857891953839898327763102581391360))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            207691874380078731368887986759401472
                            219375176137082207647782351851749376))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            2866147865911224850948833973729492992
                            2876532459637965912762811999785582592))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            208993117721213008849524352599719936
                            218079637233320511330322344249917440)
                          256)
                        512))))))
            32768)))
      262144)
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          266510213154875632517213315586209087488
                          128)
                        256)
                      512))
                  4096)
                8192)
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          266510213154875632517213315586209087488
                          128)
                        256)
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            87729047721804447611651265978502742016
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85236745229707730349956627740477095936
                            2834994084760015885177650995754172416)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))))))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298411685053713613466904685032937357312
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775250124969483229208768984121344
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311703965071138636586551681365261156352
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297750316310682986460611715771941257216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311874836776088613319548484750483128320
                            128)
                          256)))
                    2048))
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298414930308575444408592834348149899264
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13293740301438176919543611157924282368
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297750965278465056662703394421112569856
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309215566883314757897567266343904870400
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298411685113134735361826310267097579520
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13458433457322273213727507237641912320
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298416238523994879941335178948005330944
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292442217164675930532956485699239936
                            128)
                          256)))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85070591730234615870455337876369440768))
                      1024)))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            180775007466362639972049928994898837504
                            265845599218880176545030425801025126400)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            298411685113134735352602938228095320064)
                          (Code.joinWords 128
                            309087047434630042833206226816948240384
                            311745503448492466692707602919090814976)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          1298074214633711518818642509692928))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            130264343606728796173139176305859756032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            2834994084760015885177650995754172416)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            127605887595351923808565310576071278592))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            42701449364590422417034801811506069504)
                          (Code.joinWords 128
                            266510213154875632531084402438510215168
                            42701449364590422417649543160642142208)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85070591730234615870455337876369440768)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            87729047741611488240217350376888729600
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499473114484112975882535043072)
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            2834994084760015885177650995754172416)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))))))))))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          256))
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85070591730234615870455337876369440768))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Code.joinWords 128
                            180775007466362639972049928994898837504
                            266510213216772634481482329331165298688))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            127605887635120747560808319118047444992
                            45193751859327433668767790167090003968)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85071889804449249577362470500451745792)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127772041094825038287490139687875510272
                            2834994084760015885177650995754172416)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256))))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            309087047394861219080963218274972073984))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895022100482527518296040322105344
                            128)
                          (Code.joinWords 128
                            255876389188596305547853945956267458560
                            309253200894334333569726160772767154176)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298094021674335473217022468292608
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85070591730234615870455337876369440768)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298094021674335473217022468292608
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Nat.shiftLeft
                            2824609491042946229920590003095732224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            85236745229707730354568313758904483840
                            2834994084760015885177650995754172416)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Nat.shiftLeft
                          85071889804449249577362470500451745792
                          256))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            98363033967167644436811198437141774336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710541853257309349571011410214780928
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298411685053713613466904685032937357312
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            87729047721804447611651265978502742016
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2711677668195113843114752456286797824
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            95707021986148012089300046314278486016
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43369967726331583300043315187518799872
                            128)
                          (Nat.shiftLeft
                            10679915742103625404847730450151505920
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183500083312988819472512656080896
                            128)
                          (Nat.shiftLeft
                            266510213214296754402911568781367050240
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Nat.shiftLeft
                            45235290231555418299757684020165476352
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            87729047741611488240217350376888729600
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710420158799687439550719560880488448
                            128)
                          256)))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292442217125987942401462180813733888
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            2711839927471943056478144034297085952
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            166153499473114484112975882535043072
                            128)
                          (Nat.shiftLeft
                            2876532459628294506208146766201618432
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2659916325061294666078138322653282304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710379593980480136353986820094033920
                            128)
                          256)))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            309214268809100124186003270417877303296
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298581742917035430911409328816627122176
                            128)
                          (Nat.shiftLeft
                            309257105258183036518550333031020756992
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2699994366438110366979973279270305792
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            2711677668195113843258867644362653696
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42537892013546575346736091177135636480
                            128)
                          (Nat.shiftLeft
                            10638377367235346783817093392459890688
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170057863321817430669726465895956480
                            128)
                          (Nat.shiftLeft
                            10679915742103625404847730450151505920
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2866147865911224850948833973729492992
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            166153499473114484112975882535043072
                            128)
                          (Nat.shiftLeft
                            2876532459628294506208146766201618432
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2701333639297251491342654546206785536
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710420158799687439694834748956344320
                            128)
                          256)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            265845599156983174580761412056068915200))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            309087047394861219071163385485813874688)
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            309087047394861219071163385485813874688)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          85070591730234615870455337876369440768)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            1298074214633706907132624082305024)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007466362639972049928994898837504
                            128)
                          (Code.joinWords 128
                            266510213194489713774345484382981062656
                            266510213216772634481482329331165298688))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            42535295865272050437832498463333416960
                            45193751856696811085286357082929364992)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591750041656494409736256328040448)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          85070591730234615870455337876369440768
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            2658455991569831745807614120560689152)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2824609491042946229920590003095732224
                            128)
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2834994084760015885177650995754172416)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            19807040628566084398385987584)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
                            128)
                          (Code.joinWords 128
                            266510213154875632526436687623063863296
                            42535295865117307933498286681274449920))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            42701449364590422417034801811506069504)
                          (Code.joinWords 128
                            266510213154875632531084402438510215168
                            42701449364590422417037053611319754752)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          85070591730234615870455337876369440768
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            19807040628566084398385987584)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            1298074214633706907132624082305024)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            87895201221277562095764241861037785088
                            2824609491042946229920590003095732224))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            2834994084760015885177650995754172416)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            1298074214633706907132624082305024)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2432 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage038
