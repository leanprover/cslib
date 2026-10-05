/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2049–2112 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage032

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338510668721749769393343847788122734592
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            317243101849350145345822370064955867136)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075513629888335555563689791717376
                            219628775737421631162970255338242048)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            2876532459628294508703140959764873216)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            21485806164080831447702883125918957568)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075513629888335555563689791717376
                            218238727528720104947300887877910528)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075513630492798465371004379070464
                            51923602604078882768880592668852224)
                          256)
                        512)))))
              16384)
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          (Code.joinWords 128
                            319848082634174649331292839128122523648
                            333192447819885985549979606272228458496))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319679332986272267433365597997422870528
                            333013151318989704783431912570860077056)
                          (Code.joinWords 128
                            149706899233281281990214461141758771200
                            220834937826579726222348299305746432))
                        512)
                      1024)
                    2048)
                  4096))
              16384)
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
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779608898499145501568964048715776)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779648512580402633737760820690944)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            42537892053160656603868259973907611648)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779648512580402633737760820690944)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          2596188043348670946434044936585216)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            42535295904731389190053994725743001600)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            39614081257132168796771975168)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            42535295914634909504337036924935995392)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14164585830083009770631193986112421888
                            128)
                          (Nat.shiftLeft
                            2879128608057561920020160214552543232
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            872305872233851041593123383308976128
                            128)
                          (Code.joinWords 128
                            42537892013546575346736091177135636480
                            220834875929577761953334554349535232))
                        512)
                      1024)
                    2048)
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        256)
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        256))
                    1024))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            42537892013546575346736091177135636480
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            2712985249789249262321249595248607232
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779648512580402633737760820690944)
                          256)
                        (Nat.shiftLeft
                          170143779608898499154724941000903491584
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596188043348670946434044936585216)
                          256)
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          2596148429267423037637285019385856
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295875020828247204868128164020224)
                          256)
                        (Nat.shiftLeft
                          42535295865117307935227668938184720384
                          256))
                      1024))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            22098415429924226387025792377160728576
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            21436397580461035864388154095185166336
                            5537746858904222879191165913123520512))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298577838553186727951017660915472400384
                            338506601457371296883596863966493540352)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            22098415429924226387025792377160728576
                            872305872233851041593123383308976128)
                          (Code.joinWords 128
                            168749648057728865747720979649396736
                            179296501061299140925090583715774464))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          170143779608898499145501568964048715776)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            170143779608898499145501568964048715776)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            10636582413599504867540282105189629952)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            10633823966279326983230456482242756608)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          2596148429267413814265248164610048))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            53169282100576984443798716188417064960)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316911983139663491615228241121378304))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            10636582413599504867540282105189629952)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            10636582416075384946111042654987878400)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            10633823966279326983230456482242756608)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            42701449364590422417034801811506069504)
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            2834994084760015887636616392298463232)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            53169282093149344208086434539022319616)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267729062197068573142613151537168384
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986228032036275164608610051293184
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            53169282103052864522369476738215313408)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Nat.shiftLeft
                            4398046511104
                            128))))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            2596148429267413814265248164610048)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332309595094658235639766030318250754048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381917478573879957913600
                            128)
                          (Nat.shiftLeft
                            333192295701813958162451426667843813376
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499154724941000903491584
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            170143779608898499154724941000903491584
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          42537892013546575355959463213990412288
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329648542954659136480144150949525454848
                            128)
                          (Nat.shiftLeft
                            162168411634189003922490245409952235520
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            330520848826892987521737274332834430976
                            128)
                          (Nat.shiftLeft
                            2712985249789249276192336447549734912
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499154724941000903491584
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307942145197965825802240
                            21267647932558653966460912964485513216)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          2596148429267423037637285019385856
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            10141204801825835211973625643008)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            21267647932558653966460912964485513216))
                        (Nat.shiftLeft
                          42535295865117307944451040975039496192
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          2596148429267413814265248164610048)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584559915698317458076141205606891520)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316911983139663491615228241121378304))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            316356262996809977751106080346722009088)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            317238953462760898462694294503259373568)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584641045336732064757836994612035584
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267729062197068573142613151537168384
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319670390845760118792885067296276480)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            162259276829213363391578010288128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Nat.shiftLeft
                            4398046511104
                            128)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          2596148429267413814265248164610048)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          2596148429267413814265248164610048)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21599954931504882934686864729555599360
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            332312069548629881143557751882907648)
                          256))))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26916871985246947339219698957489799168)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            332317140151030794061163738695729152)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584559915698317458076141205606891520))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5649224052688293372758785993004285952))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332393199187044487825253540888051712
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          (Code.joinWords 128
                            298577838553186727951017660915472400384
                            317571260461707127416182216487759511552))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21600041131745698454286170903420076032)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            7975367974709495240161030935123329024)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            3167301083706244855862568157368549376)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584641045336732065046067370763747328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21600041131745698454286170903420076032
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5317074242416492705266850195283378176
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            332479399427860007424555316706017280)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316993112778078098585154406278234112))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Nat.shiftLeft
                            332312069548629881143562149929418752
                            128))))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333526063668076950181779965200157376512
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420875716138695094268735170543616
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2876532472675021951486973019816984576
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            23978032600246095627453942768397713408
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807087646766929874518016
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2711855211970385508952517999945842688
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807087646766929874518016
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2710389104464503353419074718503272448
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807087646907667362873344
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51923605515209002988394433010991104
                            128)
                          256)))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          2596148429267413814265248164610048)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          2596148429267413814265248164610048)
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            332306998946228968225951765070086144)
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            26916948044282961032983788759682121728)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706096627177656826174898176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Nat.shiftLeft
                            5317074242416492704978619819131666432
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            5649300111724307066522875795196608512)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316993112778078098296924030126522368)
                          256)))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            312254348540706251052758927826535579648)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            21267653003161056059970139668709638144)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Code.joinWords 128
                            334913288580298207875428986860339200
                            10141204801825835211973625643008)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          21267647932558653966460912964485513216)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            1180591620717411303424)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5316998183380479011214530016939343872)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            498460508438920645304974247569915904
                            8151906078460855336946279707108704256)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002184655100059806983549616128
                            26584646115939134158267063698836160512)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685053713613466904685032937357312
                            128)
                          (Nat.shiftLeft
                            317571260461707127416182216487759511552
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            26584646115939134158267063698836160512)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            332317140228402046516500005876924416
                            5317084383621294530813831792757309440)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          21267647932558653966460912964485513216)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            332312069626001133598894019064102912
                            5316993112778079278888544747537825792))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            34559927890407812695498983567288958976
                            128)
                          (Nat.shiftLeft
                            23928700072557753126082792333210812416
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            3045292248735478229968348070713229312
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            667220287526527185324752788785201152
                            332306998946228968225951765070086144)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          664613997892457936451903530140172288))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            21267647932558653966460912964485513216))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43199920004214567697514784441950535680
                            332306998946228968225951765070086144)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333521996411126117905475448815728197632
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            34559927890407812695498983567288958976
                            128)
                          (Nat.shiftLeft
                            2661052139999099160198480858517078016
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13333818332717437350066314573437206528
                            128)
                          (Nat.shiftLeft
                            2671446874920970641293005624614846464
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            667220287526527185324752788785201152
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            2834994095321191845331051465987325952)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43199920004214567695244970229755805696
                            21267653003161056059970139668709638144)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            667220287526527185360781585804165120
                            5070602402093509226704224124928)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            664624139097259762323144300784779264
                            10141204801825835211973625643008))
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          42535295865117307932921825928971026432)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43199920004214567697550813238969499648
                            1180591620717411303424)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319508131568930905429493489285988352)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332388128584643574907647554075230208)
                          256)))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          2596148429267413814265248164610048))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584559915698317458076141205606891520))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            5649218982085892459841180006191464448))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            146215079536340746036424368823788896256))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            298577838553186727951017660915472400384)
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            2834994084760015902230530984792555520)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584641045336732065046067370763747328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            21600036061143297541368564916607254528)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            5319670390845760119081115443447988224)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267729062197068573430843527688880128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225956163116597248)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2596148429267413814265248164610048)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            334903147375496382040217013234696192
                            2596148429267413814265248164610048)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5316917053742064404532834227934199808)
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267729062197068573142608753490657280)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            21267653003161054879378518951298334720)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            86200240815519599301775817965568)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            311039351013670314259490852105600630784)
                          (Code.joinWords 128
                            128768962161220481144903613160552923136
                            2834994157421293347295322912294174720)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002184655100059806983549616128
                            26584564986300719551585367909831016448)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2606289634069239649477221790253056
                            128)
                          (Code.joinWords 128
                            334913288657669460330765254041534464
                            10141204801825835211973625643008)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5316911983139663491615228241121378304))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            21267653003238427312425475935890833408
                            5316911983139664672206848958532681728))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070679772165372942253994016768
                            86200240815519599301775817965568)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            166153509492691677079022482499829760
                            176538103751360099523437345426636800)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969930563203366912
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267653003238426131833855218479529984
                            21267653003161056059970144066756149248)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            42535295865117307932921825928971026432)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            2658455991569831748545802694001950720))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            42701449364590422417034801811506069504)
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            2668840585286901403523640509763420160)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267729062197068573430839129642369024
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070679773345964562971405320192
                            21267729062197069753734233868948471808)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213651621954161999872
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            172400481631039198603551635931136
                            128)
                          (Code.joinWords 128
                            10141282173078290548240806838272
                            172400481631039198603551635931136)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            288234774198222848
                            128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            77372433046956984592498688
                            1180591625115457814528)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2048 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage032
