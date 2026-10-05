/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 321–384 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage005

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            256212605621993638375521673614496628736)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Code.joinWords 128
                            256212605621993638361683026701721796608
                            256212605621993638361683026701721796608))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          256208696187542534516046120724132265984
                          256208696187542534516046120724132265984)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          256212605621993638375520547663050178560
                          4614148958833344512)
                        256)
                      512))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      128
                      128)
                    256)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      128
                      128)
                    256))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          864691128455135232
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          19439959438354394641218178256600039424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          19439959438354394641218178256600039424
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          19439959438354394642226984573131030528)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          19439959438354394642226984573131030528)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        11529215046068469760
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          11529215046068469760
                          1008806316530991104)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          6147679480505235912180107653796593664)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          6147679480505235912180107653796593664)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539676138344690923601920
                          6147679480505235913188913970327584768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539676138344690923601920
                          6147679480505235912612453218024161280)
                        256))
                    2048)))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  576460752303423488
                  1024)
                4096)
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255381825448122063658824132322014527488
                          128)
                        (Nat.shiftLeft
                          256212605621993638361683026701721796608
                          128))
                      512)
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    2606289634069239649477221790253056
                    512)
                  1024)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2658455991569831745807614120560689152
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2658455991569831745807614120560689152
                        256)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        12676506002282294014967032053760
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256)
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          74644459638296681987754415228868100096
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658456625395131859922314868912291840
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          31945616563340328810369090639152283648
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658456625395131859922314868912291840
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256)
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256)
                      (Nat.shiftLeft
                        830767497365572420564879412675215360
                        256))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    35184372088832
                    128)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1099511627776
                      1024)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255381822912820863202365329328608116736
                            85240641987652831927136828606130421760)
                          (Code.joinWords 128
                            3909434451103859474215832685379584
                            3909434451103859474215832685379584))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      141287244169216
                      256)
                    512))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        255461005439913519323700419397628723200
                        255461005439913519323700419397628723200)
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256212590410186435622930208741283332096))
                    512)
                  1024)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10141204801825835211973625643008
                          633825300114114700748351602688)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          41538374868278621028243970633760768)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          12676506002282294014967032053760
                          633825300114114700748351602688)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          41538374868278621028243970633760768)
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809510892867710640717824
                          319014718988379809510892867710640717824)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484185033476572971008
                          41538374868278621028243970633760768)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            41538374868278621028243970633760768)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484185033476572971008
                            41538374868278621028243970633760768)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          41538374868278621028243970633760768)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            51922968585348276285304963292200960)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            51922968585348276285304963292200960)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    154742504910672534362390528
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        166153499473114484112975882535043072
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        166153499473114484112975882535043072
                        256)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          257874165969736787767400815461136334848
                          128)
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128))
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          67167552162006530202670500514791161856
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21976558713025487151118717291434344448
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166154133298414598227676630886645760
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166154133298414598227676630886645760
                          128)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        202824096036516704239472512860160
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256)
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256)))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256)
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256)
                      (Nat.shiftLeft
                        13292279957849158729038070602803445760
                        256)))
                  4096)
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    154742504910672534362390528
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Nat.shiftLeft
                        166163640677916309948187856160686080
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        10775030101939949912721977245696
                        256)
                      (Nat.shiftLeft
                        166164274503216424062888604512288768
                        256)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        66464158196951890272368009840192126976
                        128)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        895595149061244072157420814598144
                        128)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          67167552162006530202670500514791161856
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21976558713025487151118717291434344448
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            40564819207303340847894502572032)
                          256)
                        512)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          166154133298414598227676630886645760
                          128)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166154133298414598227676630886645760
                          128)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        651572408517309912369305447563264
                        40564819207303340847894502572032)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          895595149061244072170649313869824)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          1329227995784915872903807060280344576)
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329230531086116329434667647724683264
                            40564819207303340847894502572032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016))))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024)))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166164274503216424062888604512288768
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166164274503216424062888604512288768
                          128)
                        256)))
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          66461399789245793645190353014017228800
                          128)
                        (Nat.shiftLeft
                          67170148310435797616484765762955771904
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          66464158196951890272368009840192126976
                          128)
                        (Nat.shiftLeft
                          21976558713025487151118717291434344448
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            166154133298414598227676630886645760
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            176538727015484253484737623545085952
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658618884671961073285706446922579968
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658618884671961073285706446922579968
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      651572408517309912369305447563264
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          63969097297149076383495714775991582720
                          74647055786725949401568680477032710144)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
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
                            2658456625395131859922314868912291840
                            20282409603651670423947251286016)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          63971703586783145623145191997781835776
                          31945616563340328810369090639152283648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
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
                            2668841219112201515179375861570732032
                            20282409603651670423947251286016))))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      651572408517309912369305447563264
                      256)
                    512)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166164274503216424062888604512288768
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          166154133298414598227676630886645760
                          128)
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            732702046931916594065094452707328)
                          256)
                        512)
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        512)
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          66461399789245793645190353014017228800
                          128)
                        (Nat.shiftLeft
                          67170148310435797616484765762955771904
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          23928862331834582339446183911221100544
                          128)
                        (Nat.shiftLeft
                          21976558713025487151118717291434344448
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            40564819207303340847894502572032)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            166154133298414598227676630886645760
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10775030101939949912721977245696
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            176538727015484253484737623545085952
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    689601926524156794414206543724544
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        651572408517309912369305447563264
                        40564819207303340847894502572032)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016))))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2606289634069239649618509034422272
                          732702046931916594078322951979008)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          1329227995784915872975864654318272512))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            20282409603651670423947251286016)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
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
                            1329230531086116329434667647724683264
                            40723275532331869523081590472704)
                          256))
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
                            72057594037927936
                            20282409603651670423947251286016))))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))
                      1024)))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648811118518924402394138102726656
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        232113757366008801543585792
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14455354454160960117828901780548747264
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14455354454160960117828901780548747264
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          14455354454431759501422578715682930688
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          256)
                        (Nat.shiftLeft
                          14455354454431759501422578715682930688
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2048
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2048
                      256)
                    512))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199553631364631810525745905664
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199553631364631810525745905664
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166648811113682999763006736889282560
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19817618877061664993341079552
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          196608
                          128)
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128)))
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      49517601571415210995964968960
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        49517601571415210995964968960
                        256)
                      (Nat.shiftLeft
                        270799383593676935134183424
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          13624586956795387697264022367873531904
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          13624586956795387697264022367873531904
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479375104141236024340640820101120
                          256)
                        (Nat.shiftLeft
                          13624586957066187080857699303007715328
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479375104141236024340640820101120
                          256)
                        (Nat.shiftLeft
                          13624586956911444575947026768645324800
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3541774862152233910272
                        128)
                      256)
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      13194139533312
                      128)
                    256)
                  512))
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        19342813113834066795298816
                        256)
                      (Nat.shiftLeft
                        19342813113834066795298816
                        256))
                    2048)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      72057594037927936
                      256)
                    (Nat.shiftLeft
                      72057594037927936
                      256)))
                8192)
              16384)))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  576460752303423488
                  1024)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          705447559027009661932915333791744
                          128)
                        256)
                      512))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      63971703586783145623145191997781835776
                      512)
                    1024))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          705447559030699010747657244114944
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        512)
                      (Nat.shiftLeft
                        2658618250846660959171005698570977280
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        162893102129327478092326361890816
                        256)
                      (Nat.shiftLeft
                        2658618884671961073285706446922579968
                        256))
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2535301200456458802993406410752
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          74644459638296681987754415228868100096
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          2658456625395131859922314868912291840)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          31945616563340328810369090639152283648
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658456625395131859922314868912291840
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83117314575107358511169902565392384)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    35184372088832
                    128)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1099511627776
                      1024)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          705447559027009661932915333791744
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          141287244169216
                          13228499271680)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          20769504346789367572598259399524352)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719047858959821953449862826557440
                          319014719047858959821953449862826557440)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          705447559030699010747657244114944
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401513883074560
                            1267650600228229401496703205376))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        (Nat.shiftLeft
                          1125899906842624
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            103845937170696552570609926584401920
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          1125899906842624)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      649037107316853453566312041152512
                      256)
                    (Nat.shiftLeft
                      2535301200456458802993406410752
                      256))
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        689601926524156794414206543724544
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2535301200456458802993406410752
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809510748752522564861952
                          13979173243358019584)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809510892867710640717824
                          4755801206503243776)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207377127824189340778496
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            73786976294838206464)
                          256)
                        1267650600228229401496703205376)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242128545535305449472
                          83076749755900055170322008062820352)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83117314575107432298146197403598848)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900128957298302901026816)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        72057594037927936
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228301459090741133312
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          17179869184
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          1125899906842624
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          20770772002225299079332372894711808)
                        256)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    151115727451828646838272
                    512)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        642241841670271749062656
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          257874125404917580464059967566633762816
                          128)
                        (Nat.shiftLeft
                          4137611559144940766485239262347264
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          87732982509267556035713511745252229120
                          128)
                        (Nat.shiftLeft
                          4137611559144940766485239262347264
                          128)))
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014719047839617008839615796031258624
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014719047839617008839615796031258624
                          128)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991589174558921448187355987968
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991589174558921448187355987968
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      295147905179352825856
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          202824096036516704239472512860160
                          256)
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        259199459178058595216242376754667192320
                        128)
                      (Nat.shiftLeft
                        271162511140122838072376640297190293504
                        128))
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        259199459178058595216242376754667192320
                        128)
                      (Nat.shiftLeft
                        271166405362766739193098038169437208576
                        128)))
                  1024)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    151115727451828646838272
                    512)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      649037107316853453566312041152512
                      40564819207303340847894502572032)
                    256)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          642241841670271749062656
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3689348814741910323200
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          895595149061244072157420814598144
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719047800931382611947662440660992
                          319014719047839617008839615796031258624)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          59459807511925921328748560384
                          19845726254793752531976585216)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458803010586279936
                            40564819207303340847894502572032)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          19342813113834066795298816)
                        (Nat.shiftLeft
                          17179869184
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813113834066795298816
                            20769504351625070849930876191506432)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      295147905179352825856
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        651572408517309912369305447563264
                        40564819207303340847894502572032)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809510964925304678645760
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          319014718988379809510964925304678645760)
                        256))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603725457400242089492480
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2596148429267413814265248164610048
                          895595149061244072170649313869824)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835703278458516698824704
                            128)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835703278458516698824704
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          1349997183219055183417929045597224960)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995804258686017641127075643392
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        19342813113834066795298816
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20282428946464784258014046584832
                            73786976294838206464)
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
                            1329230531086116329434667664904552448
                            40564819207303340847894502572032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            1329227995784915872975864671498141696
                            20282409603651670423947251286016))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835703278458516698824704
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20789786756393019243022206650810368
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    651572408517309912369305447563264
                    256)
                  4096)
                8192)
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
                          (Nat.shiftLeft
                            694672528925069712020193356546048
                            128)
                          256))
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706738869019327097923960832
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          694672528928759060834935266869248
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658618884671961073285706446922579968
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2658456625395131859922314868912291840
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          689601926524156794414206543724544
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      651572408517309912369305447563264
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          63969097297149076383495714775991582720
                          74647055786725949401568680477032710144)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            20282409603651670423947251286016)
                          (Code.joinWords 128
                            2658456625395131859922314868912291840
                            20282409603651670423947251286016)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21436407721665837690223366068810809344
                          31945616563340328810369090639152283648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162893102129327478092326361890816
                          256)
                        512)
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
                            2668841219112201515179375861570732032
                            20282409603651670423947251286016))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19342813113834066795298816
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83117314575107358511169902565392384)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19342813113834066795298816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          651572408517309912369305447563264
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      651572408517309912369305447563264
                      40564819207303340847894502572032)
                    256)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282698240)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          196608
                          128)
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282698240)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            694672528925069712020193356546048
                            128)
                          256))
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            732702046931916594065094452707328)
                          256)
                        512)
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          20769504346789367571472359492681728)
                        1267650600228229401496703205376))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706738869019327097923960832
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          694672528926397877593500444262400
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            40564819207303340847894502572032)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          103846254083346609627960300760203264
                          83076749755900055170322008062820352)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      689601926524156794414206543724544
                      256)
                    (Nat.shiftLeft
                      2535301200456458802993406410752
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4
                        256)
                      (Nat.shiftLeft
                        4
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2535301200456458802993406410752
                        40564819207303340847894502572032)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            20282409603651670423947251286016)
                          (Code.joinWords 128
                            1329227995784915872975864654318272512
                            20282409603651670423947251286016))))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2606289634069239649618509034422272
                          732702046931916594069526858956800)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1349997500131705240475279419773026304
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19342813113834066795298816
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            21550060203879899825443954491392)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83117314575107358511169902565392384)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            21550060203879899825443954491392
                            1267650600228229401496703205376)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329230531086116329434667647724683264
                            40723275532331869523081590472704)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            21550060203879899825443954491392)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            20791054406993247471297803447173120
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (320 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage005
