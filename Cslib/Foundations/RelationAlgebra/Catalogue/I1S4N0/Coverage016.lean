/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1025–1088 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage016

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            256212600551391237448765420714908975104)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            256212605621993638361683026701721796608
                            256212605621993638361899762433789001728)
                          (Code.joinWords 128
                            256212605621993638375572127952532406272
                            256212605621993638375572339883398660096))
                        512))
                    2048)
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            311924799887327331583518693307742945280)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          128439261382351565458979834421378547712
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          170805797458361689668139207246024278016
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          85402898729180844834069603623012139008
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          140737488355328
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539673832501681709907968
                            128)
                          256)
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            2758407706701090087464140762251264)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155539676153539651960832
                            128)
                          256)
                        (Code.joinWords 256
                          86233676367751219080469695009312997376
                          85402898729180844834069603623012139008)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155539676153539651960832
                            128)
                          256)
                        (Code.joinWords 256
                          170805797458361689668139207246024278016
                          255876389188596305533982859103966330880))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155539676153539651960832
                            128)
                          256)
                        (Code.joinWords 256
                          85569062369858761144017791479172825088
                          85402898729180844834069603623012139008)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155541981996548865654784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4056481921334796994596764844556288
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809508442909513351168000
                            128)
                          256)
                        332312069548629881143557751882907648)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            415388819285187123200045693150429184
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809508442909513351168000
                            128)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014718988379809508442909513351168000
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            415388819285187123200045693150429184
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352)))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            256212605621993638361899762433789001728)
                          (Code.joinWords 128
                            256212605621993638375572339883398660096
                            256212605621993638375572339883398660096))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5070602400912917605986812821504
                          274877906944)
                        512)))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            140898167553201082527803548389716525056)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          70368744177664
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          70368744177664
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          70368744177664
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2305843009213693952
                            106338239662793269840519130542751350784)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4056481921334796994596764844556288
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2305843009213693952
                            106338239662793269838213287533537656832)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4056481921334796994596764844556288
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            106338239662793269838069172345461800960
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            106338239662793269838069172345461800960
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352))))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            311924647769255304195990513703358300160)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140900925960907179154981205215891423232
                            128)
                          256)
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128)
                          256)
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256))))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479365200620921741298441627107328
                            2606289634069239649617959278608384)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            103679945930500267299860342279877165056
                            128)
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128))
                        (Nat.shiftLeft
                          297747071095435236787584950299569160192
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128))
                        (Nat.shiftLeft
                          297747071095435236787584950299569160192
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            93046121964220940316629885797634408448
                            128)
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128))
                        (Nat.shiftLeft
                          297747071095435236787584950299569160192
                          256))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            2606289634069239649477221790253056)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166567622043568406461429747447496704
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751681983013143125536452640768
                            128)
                          (Nat.shiftLeft
                            271166648814816925016697519556307976192
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751742429304123856995187949568
                            128)
                          (Nat.shiftLeft
                            271166648814817888379460024963931570176
                            128))))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6646221108562993971200731090406866944
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071105338757101867992498762153984
                            3904363848702946556750583360913408)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          319014719037897411068328905463247667200
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719037897411068328905463247667200
                            1329227995784915872903807060280344576)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6646221108562993971200731090406866944
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Code.joinWords 128
                            319014719037897411068328905463247667200
                            1329227995784915872975864654318272512)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      170141183460469231731687303715884105728
                      85070591730234615865843651857942052864)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            1471108521564860220436924069838848)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          274877906944)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            549755813888
                            1303144817034619824809838632763392)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      604462909807314587353088
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Code.joinWords 128
                          19342813113834066795298816
                          19342813113834066795298816))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1329227995784915874128786158925119488)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1303144817034619824809254517211136
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        1329227995784915872903807060280344576
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      170141183460469231731687303715884105728
                      85070591730234615865843651857942052864)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2606289634069239649477221790253056
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        256)))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            3904363848702946556751133116727296
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514122260194787328
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128)
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            2758407706096627177656826174898176)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170805797458361689668139207246024278016
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85402898729180844834069603623012139008
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706096627177656826174898176
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2606289634069239649477221790253056
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            4056481921372575926459722006265856))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          85402898729180844834069603623012139008)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          170805797458361689668139207246024278016
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            20769187434158199980053463897735168))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          (Code.joinWords 128
                            85402898729180844834069603623012139008
                            20769504346789367571472359492681728))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          319014718988379809496913694467282698240)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152921504606846976
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1333365607344703055511962571291754496
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            86986184187661101530845061197070336)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1433074249868262482531767361040547840)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1412304745521473114960295001547866112)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            1433074249887605295717659021873774592)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      170141183460469231731687303715884105728
                      85070591730234615865843651857942052864)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1303144817034619824738610895126528
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            20769504346789367572598551457300480)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367572598276579393536
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            549755813888
                            1303144817034619824809288876949504)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)
                        (Nat.shiftLeft
                          90387503713374279357458880099063431168
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            20769504351625144638033362994331648)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128)
                          (Nat.shiftLeft
                            90387503713374279357458880099063431168
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706096627177656826174898176
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1303144817034619824738610895126528
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4137611559787182608155511011409920
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809514207517036385402880
                            319014719062656211871330333530332856320)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719062656211871330333530332856320
                            319014719062656211871330333530333773824)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            72057594037927936
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            262148
                            128)
                          256)))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Code.joinWords 128
                          1152921504606846976
                          1329227995784915874128786158925119488))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1333365607344703055584020165329682432
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            84379894553591861881297195784732672)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1433074249873098259670385683702218752)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            103846254107525199808355096179245056))
                        512))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      170141183460469231731687303715884105728
                      85070591730234615865843651857942052864)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      140737488355328
                      128)
                    256)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          83076749736557242056487941267521536
                          19342813113834066795298816)
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          72057594037927936))
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            1471108521564860220436924069838848)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170805797458361689668139207246024278016
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85402898729180844834069603623012139008
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      140737488355328
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37778931862957161709568
                            128)
                          256)
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            1379203853407361015479095800102912)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          85402898729180844834069603623012139008)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Code.joinWords 256
                          170805797458361689668139207246024278016
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            18889465931478580854784)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          85402898729180844834069603623012139008)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          83076749736557242056487941267521536
                          19342813113834066795298816)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1379203853369434509663548961980416
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        83076749736557242056487941267521536
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076754707660212311843107659317248
                            83076749755900055170322008062820352)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          83076749736557242056487941267521536
                          19342813113834066795298816)
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352))
                      512))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      70368744177664
                      128)
                    256)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976312018075648
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        72057594037927936
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Nat.shiftLeft
                          17179869184
                          128)))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      70368744177664
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853369434509663548961980416
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853369434509663548961980416
                          128)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352))
                      512)))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            128436655092717496219330357199588294656
                            2606289634069239649477221790253056)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
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
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9903520314283042199192993792
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106338239697494276558522880653193641984
                            3904363848702946556750583360913408)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239687552070618012170320410050560
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239687552070618012170320410050560
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239687552070618012170320410050560
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            2606289634069239649477221790253056)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271162511140122838072376640297190293504
                            128)
                          (Nat.shiftLeft
                            271166648814817888379460024963931570176
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751742429304123856995187949568
                            128)
                          (Nat.shiftLeft
                            271166648814817888379460024963931570176
                            128)))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9903520314283042199192993792
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106338239687590756244239838454000648192
                            3904363848702946556750583360913408)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          106338239687552070618012170320410050560
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106338239687552070618012170320410050560
                            1329227995784915872903807060280344576)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Code.joinWords 128
                            106338239687552070618012170320410050560
                            1329227995784915872975864654318272512)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976312018075648
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1303144817034619824809254517211136
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          128)
                        256)
                      512))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      302231454903657293676544
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          19342813113834066795298816
                          19342813113834066795298816)
                        (Nat.shiftLeft
                          73786976294838206464
                          128))
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1303144817034619824809254517211136
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      170141183460469231731687303715884105728
                      85070591730234615865843651857942052864)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2606289634069239649477221790253056
                        128)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351644034102838649610567680
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144636907171029712896
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            3909434451103859474357119929548800)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          19342813113834066795298816
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            1379203853048313588828413087449088)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170805797458361689668139207246024278016
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85402898729180844834069603623012139008
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2606289634069239649477221790253056
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37778931862957161709568
                            128)
                          256)
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            1379203853369582083616138638393344)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          85402898729180844834069603623012139008)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)
                        (Code.joinWords 256
                          170805797458361689668139207246024278016
                          (Code.joinWords 128
                            256208696187542534502208810869036417024
                            20769504351644034103964566697279488)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85402898729180844834069603623012139008
                          (Code.joinWords 128
                            85402898729180844834069603623012139008
                            20769504351625144638033088116424704))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719062656211854036510961230151680
                            319014719062656211871330333530332856320)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719062656211871330333530332856320
                            319014719062656211871330333530333773824)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813113834066795298816
                            262148)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1330607199638285307413470609242324992
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        4951760157141521099596496896
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076754707660212311843107659317248
                          86986184207003914644679127992369152)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            1433074249892441072712162156459589632)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1349997500136541017613897742434697216
                            128)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1303144817034619824738610895126528
                        128)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976312018075648
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1303144817034619824809254517211136
                        128)
                      256)
                    512)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853048313588828413087449088
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1303144817034619824738610895126528
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853369434509663548961980416
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      4951760158294442604203343872
                      256)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1330607199638285307485528203280252928
                          128))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          84379894572934674995131262580031488))
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          1412304745521473114960295001547866112)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          1412304745540815928146186662381092864))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1024 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage016
