/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2817–2880 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage044

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226636131689034252957276760603973648384
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
                            224143677078865508308053942761563357184
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226802295379230375313079322556390965248
                            128)
                          256)
                        512)
                      1024)))
                8192)
              16384)
            32768)
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807089952750679260954624
                            12249940520599552000)
                          (Code.joinWords 128
                            536870912
                            570425344))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33685504
                            128)
                          (Code.joinWords 128
                            538968064
                            226854218932122817657624954172350791680)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            11529355783556857856
                            3094887889395254164606453760)
                          (Code.joinWords 128
                            140737488355328
                            149533581377536))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3106977282915412525866680320
                            128)
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            226851449749386619090497384623625994240)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            11529355783556857856
                            212679075474015807090673335415229906944)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33685504
                            128)
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218932122817657624954171778138112)))
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            212679075523534013112748413203572064256
                            2658456044182925657277946075522531328))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953552384
                            128)
                          (Code.joinWords 128
                            49672950900418932279737319424
                            10384594336039674899751130108002304)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            2596197947473448139283558716932096
                            2661214451889022284455602901697429504))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953552384
                            128)
                          (Code.joinWords 128
                            606824093048749409959936
                            10384594336684277924662836679671808)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            9367487224930631680)
                          (Code.joinWords 128
                            49518206034325018310552322048
                            2658456004568844400145777278750556160))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953552384
                            128)
                          (Code.joinWords 128
                            10634635262663473050047414372294197248
                            11033631443356528353317442149154816)))
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            3094887877145313644409554944)
                          (Code.joinWords 128
                            140737488388096
                            149533581412352))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3106977282915412525833652232
                            128)
                          (Code.joinWords 128
                            213507246822952112085174009057530380416
                            226851449749386619090497384623626029192)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          3094887877145313644409554944)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            631097204344651976034877440
                            128)
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11033630824386508710627304699592704
                            128)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            223313061699571963275017242953272786944)
                          (Code.joinWords 128
                            49517601571415210995964968960
                            618970019642690137449562112))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            49672344076335032016826269696
                            618970019651847420041494528)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            224141070789231439068404465539773104128
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            223313061699571963275017242953272786944)
                          (Code.joinWords 128
                            49518206034325018310552322048
                            649037726286873096256449490714624))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            49672950900427939478992060416
                            649037726286873105263648745455616)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            223313061699571963275017242953272786944)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706096627177656826174898176))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            44307557604477188155813518786035712)
                          (Nat.shiftLeft
                            10385227542369769371761741010206728
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            223313061699571963275017242953272786944)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            10633986225556156196602996546751954944
                            618970019651847420041494528)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            223313061699571963275017242953272786944)
                          (Code.joinWords 128
                            604462909807314587353088
                            619612261484360409198624768))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            10633823966279933807332512430907457536
                            619614622676609043275972608)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            223313061699571963275017242953272786944)
                          (Nat.shiftLeft
                            649037726286873096256449490714624
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42188045800895588596511031026647040
                            128)
                          (Code.joinWords 128
                            10634635262663473050056421571548938240
                            649037726286873105263648745586688)))
                      1024))))))
          65536))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075523534013112748413206256451584
                          (Code.joinWords 128
                            536870912
                            570425344))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            49711636526646600413866885120
                            2228224)
                          (Code.joinWords 128
                            538968064
                            226854218932122817657624954172350791680)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            212679075474015807089952750676576567296
                            12105825331953270784))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39652766883359836930362572800
                            2417851639229258349543424)
                          (Code.joinWords 128
                            166153499473114495687368212121387008
                            10384593717069655266068191913181184)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            226633373281328156330099103777798750208)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            11529215046068469760
                            619612273590036207570518016))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            9007199254740992
                            619614622676609043275972608)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            11529355783556825088
                            618970031748515469402832896))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            649037107316853462573511295893504
                            649037726286873105263648745455616)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49518206034325018310552354816
                          (Code.joinWords 128
                            604462909807314587353088
                            225968759283435698393647200247658577920))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            49711636526691636959367954560
                            47851330158592000)
                          (Code.joinWords 128
                            606824093048749409959936
                            226851449749386619090497384623625994240)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          49518206034325018310552354816
                          (Code.joinWords 128
                            39614081257132168796771975168
                            225971517691141795020824857073833476096))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075523727443605069995308497240064
                            2228224)
                          (Code.joinWords 128
                            39768823762042841331134365696
                            226854218932122817657624954171778138112)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            604462909807314587385856
                            225968759283435698393647200247658612736))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            45036546029551744
                            47851330157019272)
                          (Code.joinWords 128
                            606824093048749409992832
                            226851449749386619090497384623626029192)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          (Code.joinWords 128
                            45036546029551744
                            11822533137530880)
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11033630824386508710627304699592704
                            128)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2596148429267425343621031721435136
                            149533581377536))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39652766883359836930362572800
                            2417851639229258349543424)
                          (Code.joinWords 128
                            168759789107183735336845433911640064
                            10384593717069655266218275250372608)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            11529355783556825088
                            665273176204576615740681815806967808))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39652766883359836930362572800
                            2417851639229258349543424)
                          (Code.joinWords 128
                            166153499473114486463996175266611200
                            11033630824386508719634503954333696)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            2758407706096627177656826174898176)
                          2596148429267413814265248164610048)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            44307557604477188155813518786035712)
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            10385227542369769371761741010206728)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019774976
                          (Code.joinWords 128
                            140737488355328
                            664613998511427956094743201171111936))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            9148486498910208
                            618970019651847420041494528)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019774976
                          (Nat.shiftLeft
                            664624139716872023771475912964440064
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            9007199254740992
                            619614622676609043275972608)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019774976
                          (Nat.shiftLeft
                            665273176823546635383371953256529920
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            42188045800895588596511031026647040)
                          (Code.joinWords 128
                            649037107316853462573511295893504
                            649037726286873105263648745586688)))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          2684387328
                          (Code.joinWords 128
                            536870912
                            570425344))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            538968064
                            10384593717069655257060992694222848)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            10384593717069655257060992658440192)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            224016455664626603205319733627871821824)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            224016455664626603205319733627871821824
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            49518206045854374094109147136
                            618970031748515469402832896))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            49672950900427939478992060416
                            649037726286873105263648745455616)))
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007466362639972049928994898837504)
                          (Code.joinWords 128
                            213341093363093078858193201971767279616
                            226674911698286396286830277095002734592))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            10633823966279931457669478842898579456
                            619612273590036207570518016))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            10633823966279933807332512430907457536
                            619614622676609043275972608)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            10633823966279326994759812265799581696
                            618970031748515469402832896))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782173977334906880
                            128)
                          (Code.joinWords 128
                            10634635262663473050632882323852361728
                            649037726286873105263648745455616)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613997892457936451903530140172288
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            212676479325586539664609129644855164928
                            225968759283436302856557007562245965824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            688136
                            128)
                          (Code.joinWords 128
                            213507246822952112085174149795018735744
                            226851449749387225914590582906617366664)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            10384593717069655257060992658440192)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613997892457936451903530140172288
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            664613998047200441362576064502562816
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041283584
                            128)
                          (Code.joinWords 128
                            10633823966279326983806917234546180096
                            649037107316853453566312041152512)))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            664614047410059507867255263593496576
                            664613998511427956094743201171111936))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Code.joinWords 128
                            49672344076335032016826269696
                            618970019651847420041494528)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            223310303291865866657062958163952664576
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170805797458361689677362579282879053824
                            128)
                          (Nat.shiftLeft
                            224182609164099717698692110344280604672
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            664614047410663970776921840692494336
                            665273176978289140294044487618920448))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735143507668938915840
                            128)
                          (Code.joinWords 128
                            49672950900427939478992060416
                            649037726286873105263648745455616)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164642816
                            2758407706096627177656826174898176)
                          (Code.joinWords 128
                            11298437964171784919682360012382928896
                            664613997892457936451903530140172288))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            41711409175209774341548270621425664)
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            10385227542369769371761741010206728)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            11298437964171784919682500749871284224
                            664613998511427956094743201171111936))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782173977334906880
                            128)
                          (Code.joinWords 128
                            10633986225556156197179457299055378432
                            618970019651847420041494528)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            11298437964172389382592167326970281984
                            664624139871614528682148447326830592))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735143507668938915840
                            128)
                          (Code.joinWords 128
                            10633823966279933807332512430907457536
                            619614622676609043275972608)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            665273176978289140294044487618920448)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42188045803313440236303239329480704
                            128)
                          (Code.joinWords 128
                            10634635262663473050632882323852361728
                            649037726286873105263648745586688)))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2816 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage044
