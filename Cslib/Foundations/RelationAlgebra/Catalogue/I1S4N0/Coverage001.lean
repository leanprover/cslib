/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 65–128 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage001

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            256212605621993638361683026701722632192
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            256208696187542534502208810869036417024
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            256212605621993638361683026701721796608
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256208696187542534516043868924318580736)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256212605621993638375518295863236493312)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256208696187542534516043868924318580736)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            256208696187542534502424983651150200832
                            128)
                          256208696187542534502208810869036417024)
                        512))))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          604462909807314587353088
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648751681983013143125536453476352
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199543959958074893492348256256
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648811104011593206089703491633152
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199543959958074893492348256256
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          256)
                        (Nat.shiftLeft
                          271162511140180866511718142497576189952
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            524288
                            128)
                          256)
                        (Nat.shiftLeft
                          524288
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            524288
                            128)
                          256)
                        (Nat.shiftLeft
                          524288
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          104894781136120587751573086842904379392
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          104894781136120587751573086842904379392
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          104894781136120587751573086842904379392
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          104894781136120587751573086842904379392
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            104894781136120587757193579177862889472
                            128)
                          256)
                        (Nat.shiftLeft
                          104894781156198427763732848176424681472
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            104894781136120587757193579177862889472
                            128)
                          256)
                        (Nat.shiftLeft
                          104894781156198427763732848176424681472
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        59421121885698253195157962752
                        58028439341502200385896448)
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256208696187542534502208810869036417024))
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256208696187542534502208810869036417024)
                      256)
                    512)
                  2048))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        77371252455336267181195264
                        256)
                      (Nat.shiftLeft
                        77371252455336267181195264
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      1180591620717411303424
                      256)
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256))
                    2048))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        (Nat.shiftLeft
                          256212605621993638361683026701721796608
                          128))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      144115188075855872
                      2199023255552)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        (Nat.shiftLeft
                          256212605621993638361683026701721796608
                          128))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        72057594037927936
                        512)
                      1024)
                    2048)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256))
                    (Nat.shiftLeft
                      4398046511104
                      256))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1099511627776
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            319014718988379809510748752522564861952)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          167700803936957862746277970441150660608
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5337762617124867465868396389619204096
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          20850633985203974253168148497825792)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          415383748682786210282439706337607680)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          415383748682786210282439706337607680)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            415383748682786210282439706337607680
                            415383748682786210282439706337607680)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            415383748682786210282439706337607680
                            415383748682786210282439706337607680)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))
                    2048)))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        255211775190703847597530955573826158592
                        255211775190703847597530955573826158592)
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256212605621993638361683026701721796608))
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          216172782113783808
                          128)
                        (Nat.shiftLeft
                          3909434451103873363317083495989248
                          128))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1099511627776
                        128)
                      512)
                    2048)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17867063951360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          274877906944
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          83076749736557242074502339777003520)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          83076749736557242074502339777003520)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          83076749736557242074502339777003520)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          415383748682786210282439706337607680
                          83076749736557242074502339777003520)
                        256))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        604462909807314587353088
                        256))
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        38685626227668133590597632
                        128)
                      (Nat.shiftLeft
                        590295810358705651712
                        128))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        271166648751681983013143125536452640768
                        128))
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719047800931382611947662440660992
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          152746988984377559176110141012996784128
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          353081573895419248715030111375589376
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        (Nat.shiftLeft
                          20774574949190280489078346305503232
                          128)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        295147905179352825856
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128))
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        19342813113834066795298816
                        128)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6646139978924579364519035301401722880
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6646139978924579364519035301401722880
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        604462909807314587353088
                        256))
                    (Nat.shiftLeft
                      1180591620717411303424
                      256))
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59421121885698253195157962752
                          58028439341502200385896448)
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282698240))
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        38685626227668133590597632
                        128)
                      (Nat.shiftLeft
                        590295810358705651712
                        128)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719047800931382611947662440660992
                            319014719047800931382611947662440660992)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          152746988984377559176110141012996784128
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          353081573895419248715030111375589376
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        (Nat.shiftLeft
                          20774574949190280489078346305503232
                          128)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4835703278458516698824704
                          256)
                        20282409603651670423947251286016)
                      (Nat.shiftLeft
                        4835703278458516698824704
                        256)))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        73786976294838206464
                        256)
                      (Nat.shiftLeft
                        368934881474191032320
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20789786756393019241896306743967744
                            20789786761228722520354823442792448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            20282409603651670423947251286016
                            20282409603651670423947251286016)))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          19342813113834066795298816
                          128)
                        (Code.joinWords 128
                          20769504346789367571472359492681728
                          20769504351625070849930876191506432))))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20789786756393019241896306743967744
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769504346789367571472359492681728
                          20769504351625070849930876191506432)
                        256)))
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256))
                    (Nat.shiftLeft
                      5649218982085892459841180006191464448
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1180591620717411303424
                          128)
                        256)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2330734084844628283326875930984448
                          128)
                        256)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2558911192885709575596282507952128
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719047800931382611947662440660992
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            151531991519482827362673234130308694016
                            128)
                          (Nat.shiftLeft
                            152746988984377559176110141012996784128
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          (Nat.shiftLeft
                            2330734085150549087045275134984192
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            325786204258654956184652723781632
                            325786204258654956184652723781632)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            353081573895419248715030111375589376
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        (Nat.shiftLeft
                          20774574949190280489078346305503232
                          128)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4398046511104
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          2596148429267413814265248164610048)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            295147905179352825856
                            128)
                          256)
                        (Nat.shiftLeft
                          1099511627776
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            319014718988379809510748752522564861952)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            149039689027383692249339929583887056896
                            8589934592)
                          (Code.joinWords 128
                            167700803936957862746277970441150660608
                            2558911192885709575679879751401472))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            5337762617124867465868396389619204096
                            20282409603651670423947251286016)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          20850633985203974253168148497825792)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1412326295581676994860120445502357504
                            83078017406500283399723504766025728)
                          256)
                        (Nat.shiftLeft
                          1329248278194519524646288601569558528
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83421550719162133567529111334682624)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83098299796761121956313385222012928
                            83078017406500283399723504766025728)
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329553781989174527932049307042054144
                            325786204258654956184652723781632)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329249545845119752803632504234835968
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          1329248278194519524646288601569558528
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1433095799928466362431592804995039232
                            103867804167729005920078328208818176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            1350019050191909120448288357672288256
                            21550060203879899825443954491392)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1412304745521473114960295001547866112
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            20791054406993247471297803447173120
                            20770772002225299079332372894711808))
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          20789786756393019243022206650810368))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    324518553658426726783156020576256
                    (Code.joinWords 1024
                      20282409603651670423947251286016
                      332306998946228968225951765070086144)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1180591620717411303424
                          128)
                        256)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282698240)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2330734084844628283326875930984448
                          128)
                        256)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17293822569103491072
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            151531991519482827362673234130308694016
                            128)
                          (Nat.shiftLeft
                            152746988984377559176110141012996784128
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          (Nat.shiftLeft
                            2330734085150549087045275134984192
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            325786204258654956184652723781632
                            1267650600228229419088889249792)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            353081573895419248715030111375589376
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        (Nat.shiftLeft
                          20774574949190280489078346305503232
                          128)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          295147905179352825856
                          128)
                        256)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)
                    512))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          344800963262078397207103271862272
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          344800963262078397207103271862272
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20789786756393019241896306743967744
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            20282409603651670423947251286016
                            20282409603651670423947251286016)))
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262144
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83078017387157470285889437970726912
                          83078017406500283399723504766287872)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83421550719162133567529111334682624)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83078017387157470285889437970726912
                          83078017406500283399723504766025728)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            325786204258654956184652723781632
                            1267650600228229419088889249792)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            103867804143550489527785744714694656
                            83078017406500283400850521364365312)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            21550060203879899825443954491392
                            1267650600228229402596214833152)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          20770771997389595800873856195887104
                          1267650600228230527413789917184)))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 32768
          (Code.joinWords 16384
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      288230376151711744
                      256)
                    (Nat.shiftLeft
                      288230376151711744
                      256))
                  2048)
                4096)
              8192)
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Code.joinWords 512
                  (Code.joinWords 256
                    (Nat.shiftLeft
                      13835058055282163712
                      128)
                    (Nat.shiftLeft
                      271162511140122838072376640297190293504
                      128))
                  (Code.joinWords 256
                    (Nat.shiftLeft
                      216172782113783808
                      128)
                    (Nat.shiftLeft
                      271162511140122838072376640297190293504
                      128)))
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))))
                4096)))
          (Code.joinWords 16384
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    4398046511104
                    256)
                  (Nat.shiftLeft
                    4398046511104
                    256))
                4096)
              8192)
            (Code.joinWords 8192
              (Nat.shiftLeft
                (Code.joinWords 512
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      271162511140122838072376640297190293504
                      128)
                    256)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      271162511140122838072376640297190293504
                      128)
                    256))
                4096)
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))))
                4096))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      128)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        1125899906842624)
                      (Nat.shiftLeft
                        1125899906842624
                        256))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          13835058055282163712
                          128)
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          216172782113783808
                          128)
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      144115188075855872
                      2199023255552)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20770771997389595800873856195887104
                            1267650600228229401496703205376)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            20770771997389595801999756102729728
                            1267650600228229401496703205376)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Code.joinWords 256
                          72057594037927936
                          20769504346789367572598259399524352)))
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256))
                    (Nat.shiftLeft
                      4398046511104
                      256))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    2048)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      17179869184
                      256)
                    (Nat.shiftLeft
                      1116691496960
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809510748752522564861952
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            319014718988379809510748752522564861952)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          167700803936957862746277970441150660608
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5337762617124867465868396389619204096
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          20850633985203974253168148497825792)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20770771997389595800873856195887104
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      128)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1267650600228229401496703205376
                      128)
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1267650600228229402596214833152
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)))
                    2048))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      17592186044416
                      128)
                    256))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      128)
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1267650600228229401496703205376
                        1267650600228229401496703205376)
                      256)
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        271162511140122838072376640297190293504
                        128))
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        128)
                      (Nat.shiftLeft
                        271166648751681983013143125536452640768
                        128)))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          94447329657392904273920
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    2048))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          58028439341502200385896448
                          128)
                        (Nat.shiftLeft
                          4137674694086944320879259117682688
                          128))
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        295147905179352825856
                        128)
                      512))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          1329227997022855912189187335179468800
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          1329227997022855912189187335179468800
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          1329227997022855912189187335179468800
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          6646139978924579364519035301401722880
                          256)
                        (Nat.shiftLeft
                          1329227997022855912189187335179468800
                          256))))
                  4096))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)
                    512)
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      512)
                    (Nat.shiftLeft
                      20282409603651670423947251286016
                      512))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        75557863725914323419136
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603946818329126604111872
                          128)
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016))))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256)
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256)))
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  324518553658426726783156020576256
                  2048)
                (Code.joinWords 2048
                  (Code.joinWords 512
                    170141183460469231731687303715884105728
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256))
                  (Code.joinWords 1024
                    1267650600228229401496703205376
                    5316911983139663491615228241121378304)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2558911192885709575596282507952128
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          325786204258654956184652723781632
                          325786204258654956184652723781632)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20770771997389595800873856195887104
                            1267650600228229401496703205376)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4398046511104
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          2596148429267413814265248164610048)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1099511627776
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            74276402357122816493948239872)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409679209534149861574705152
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            149039689027383692249339929583887056896
                            8589934592)
                          (Code.joinWords 128
                            167700803936957862746277970441150660608
                            2558911192885709575679879751401472))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            5337762617124867465868396389619204096
                            20282409603651670423947251286016)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          20850633985203974253168148497825792)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262144
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        (Nat.shiftLeft
                          1329248278194519524646288601569820672
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            344800963262078397207103271862272
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409679209534149861574705152
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329553781989174527932049307042054144
                            325786204258654956184652723781632)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329248278194519524574231007531630592
                          256)
                        (Nat.shiftLeft
                          1329248278194519524646288601569558528
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1350019050191909120375104863727517696
                            21550060203879899825443954491392)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329248278199355596859628592459415552
                            20282409603946818329126604111872)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          20789786756393019241896306743967744)
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          20282414439428735858758788317184))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  324518553658426726783156020576256
                  2048)
                (Code.joinWords 2048
                  324518553658426726783156020576256
                  21550060203879899825443954491392))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        324518553658426726783156020576256
                        324518553658426726783156020576256)
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          325786204258654956184652723781632
                          1267650600228229419088889249792)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      324518553658426726783156020576256
                      256)
                    512))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          344800963262078397207103271862272
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409679209534149861574705152
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          20282409603651670423947251286016)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          344800963262078397207103271862272
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409679209534149861574705152
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          325786204258654956184652723781632
                          1267650600228229419088889249792)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21550060203879899825443954491392
                          1267650600228229402596214833152)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603946818329126604111872
                          295147906278864453632)
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (64 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage001
