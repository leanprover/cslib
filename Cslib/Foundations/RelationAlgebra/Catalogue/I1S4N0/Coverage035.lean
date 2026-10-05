/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2241–2304 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage035

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            906694364710971881029632
                            311922041479621234956341036481568047104)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298582394489443948207486640066792521728
                            311926801032256116872157631040840531968)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234970790835885986283520
                          311922041479621234970790835885986283520)
                        256)
                      512)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249577362470500451745792
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364372586394444823104780575768051712
                            128)
                          (Code.joinWords 128
                            7097673012735901696
                            302238552576670029578240))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249577362470500451745792
                            128)
                          (Code.joinWords 128
                            70918499991552
                            70952859729920))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98362871688122460225721076612763484160
                            128)
                          (Code.joinWords 128
                            2488238794122199040
                            22292592116182000776777826304))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364372586433130449332448709358649344
                            128)
                          (Code.joinWords 128
                            70918499991552
                            302231454974610153406464))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            99028996725491704585391896079533867008
                            128)
                          (Code.joinWords 128
                            19807040635627728614102925312
                            7061644215716937728))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            99028996725491704585391896079533867008
                            128)
                          (Code.joinWords 128
                            7097673012735901696
                            7097673012735901696))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            99028996725491704585391896079533867008
                            128)
                          (Code.joinWords 128
                            19807040628566155316885979136
                            70952859729920))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            99027485685976232535945312009313058816
                            128)
                          (Code.joinWords 128
                            29749246571565033526365519872
                            2488238794122199040))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            99028996725491704585391896079533867008
                            128)
                          (Code.joinWords 128
                            70918499991552
                            70952859729920))
                        512))))))
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298582394489443948207486640066792521728
                            128)
                          (Nat.shiftLeft
                            311926801032256116872157631040840531968
                            128))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311044097097517568750370055762401558528
                            128)
                          (Nat.shiftLeft
                            311926801032256116872157631040840531968
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123047455214731149602950015478661120
                            128)
                          (Nat.shiftLeft
                            12427757428126626710101688320
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14123262955816769948601204455023575040
                          128)
                        512))))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123262975623810581778974871836950528
                            128)
                          (Nat.shiftLeft
                            29749246576138438946887041024
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123262955817072184667794130744639488
                            128)
                          (Nat.shiftLeft
                            340165058392216867700736
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123262975623810577167359222153740288
                            128)
                          (Nat.shiftLeft
                            32225126647647626233827557376
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123047455214731149602950015478661120
                            128)
                          (Nat.shiftLeft
                            12427757428126626710101688320
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14123262955817072180056178481061429248
                            128)
                          (Nat.shiftLeft
                            340157960790156991528960
                            128))
                        512))))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311926108736572067230375738653802496000
                            311926108736572067230375738653802496000)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234973202513486443184128
                          311922041479621234973202513486443184128)
                        256)
                      512)
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2488238794122199040
                          2488238794122199040)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623819150875868325216256
                            4611686018427387904)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623819150875868325216256
                            4611686018427387904)
                          (Code.joinWords 128
                            7097673012735901696
                            302238552576670029578240))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623823762632255496781824
                            70368744177664)
                          (Code.joinWords 128
                            70918499991552
                            70952859729920))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85901359227600188291020217289044656128
                          (Code.joinWords 128
                            2488238794122199040
                            32196112430465042975970820096))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623823762632255496781824
                            70368744177664)
                          (Code.joinWords 128
                            70918499991552
                            302231454974610153406464))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623819150875868325216256
                            4611686018427387904)
                          (Code.joinWords 128
                            19807040635627728614102925312
                            7061644215717462016))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623819150875868325216256
                            4611686018427387904)
                          (Code.joinWords 128
                            7097673012735901696
                            7097673012735901696))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623823762632255496781824
                            70368744177664)
                          (Code.joinWords 128
                            19807040628566155316885979136
                            70952859729920))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          85901359227600188291020217289044656128
                          (Code.joinWords 128
                            29749246571565033526365519872
                            2488238794122199040))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85902667443019623823762632255496781824
                            70368744177664)
                          (Code.joinWords 128
                            302231454974575793668096
                            70952859729920))
                        512))))))
            32768)))
      262144)
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            19807040633177770417887117312)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208)
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          29710560942849126597578981376
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            29749246573688480749596966912
                            4611686019501129728)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)
                        512)))
                  4096))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6917529027641081856
                            19807040635627728614102925312)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19807040628566084399459729408
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          29710560949766655626293805056
                          7061644216790679552)
                        256)
                      (Nat.shiftLeft
                        29749246569076794732243320832
                        256))
                    2048)
                  4096))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
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
                            85071889824256290201316868880410345472
                            128)
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            340010386766614455386112
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85902669998127864904175763260117614592
                            128)
                          (Nat.shiftLeft
                            32225126647647625649712005120
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            12427757425638387915979489280
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85901359247407228915118730857079111680
                            128)
                          (Nat.shiftLeft
                            12427757430288354532313268224
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            340010386766614455386112
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85902669998127864904319878448193470464
                            128)
                          (Nat.shiftLeft
                            340157960789572875976704
                            128))))))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311044097097517568750370055762401558528
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926801032256116872157631040840531968
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            211106232532992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311922041479621234956341036481568047104
                            128)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311922041541682650832077639794284298240
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311922041541682650832077639794284298240
                          128)
                        256))))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            29749246573688480749596966912
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            96536656223684021100769611320370659328
                            128)
                          (Nat.shiftLeft
                            29749246569076794731169579008
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            340014998452632882774016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            96536656223684021100769611320370659328
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            96536656223684021100769611320370659328
                            128)
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            12427757432700032132770168832
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            96535183213686555898205072151246012416
                            128)
                          (Nat.shiftLeft
                            12427757425638387915979489280
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            340010386766614455386112
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            96536656223684021100769611320370659328
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32196112427976804180774879232
                            128)
                          256)
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Code.joinWords 128
                            4649966615260037120
                            32196112432626770797108658176)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          19807040628566084398385987584))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          29710560942849126597578981376
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            144115188075855872)
                          (Code.joinWords 128
                            29749246573726761346429616128
                            4649966616333778944)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            302231454974026037854208
                            70368744177664)))))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          311922041479621234956341036481568047104)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          311922041479621234956341036481568047104)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        70368744177664
                        128)
                      256)
                    1024)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            302236066589675721064448)
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6917529027641081856
                            32196112435038448396491816960)
                          256)
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Nat.shiftLeft
                            32196112427976804181848621056
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Nat.shiftLeft
                            302231454903657293676544
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040633177770416813375488
                            4611686018427387904)
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          19807040628566084398385987584))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904)
                          256)
                        85071889804449249572750784482024357888)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          19807040628566084398385987584))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            29710560949766655626293805056
                            7061644216790679552)
                          256)
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          29749246569076794732243320832))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          302231454903657293676544))))))))))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311039351013670314259490852105600630784
                          311039351013670314259490852105600630784)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234956341036481568047104
                          311922041479621234956341036481568047104)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        128)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            22292592113693761981581885440
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6955809624473731072
                            22292592120649571607129358336)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Nat.shiftLeft
                            302231454903657293676544
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208)
                          256))))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        256)
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          19807040628566084398385987584)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          29710560942849126597578981376)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            29749246576032604355643310080
                            6955809625547472896)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      512)
                    1024)
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            302236066589675721064448))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        128)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            6917529027641081856
                            22292592120755406197298823168))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            38685626227668133590597632
                            128)
                          (Nat.shiftLeft
                            22292592113693761982655627264
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            19807040633177770416813375488
                            4611686018427387904))
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          19807040628566084398385987584)
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            29710560949766655626293805056
                            7061644216790679552))
                        (Nat.shiftLeft
                          29749246569076794732243320832
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        (Code.joinWords 128
                          70368744177664
                          70368744177664))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926108736572067230375738653802496000
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926108736572067230375738653802496000
                            128)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311922041549139305287460672543871991808
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311922041549139305287460672543871991808
                          128)
                        256)))
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332021575237515152246662838091776
                            128)
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332041382580375173234718517755904
                            128)
                          (Nat.shiftLeft
                            340010386766614455386112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332021575237515152246662838091776
                            128)
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          (Nat.shiftLeft
                            32225126647647625649712005120
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98362871707890815223447806859131486208
                            128)
                          (Nat.shiftLeft
                            12427757425638387915979489280
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            12427757432594197541526962176
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332041382580375173234718517755904
                            128)
                          (Nat.shiftLeft
                            340010386766614455386112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          (Nat.shiftLeft
                            340157960789572875976704
                            128))))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          12427757425638387915979489280
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          12427757425638387915979489280
                          128)
                        256))
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332021575237515152246662838091776
                            128)
                          (Nat.shiftLeft
                            29749246573688480749596966912
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          (Nat.shiftLeft
                            29749246569076794731170103296
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332041382580375173234718517755904
                            128)
                          (Nat.shiftLeft
                            340014998452632882774016
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332021575237515152246662838091776
                            128)
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            19807040628566084398385987584
                            128)
                          (Nat.shiftLeft
                            32225126647647555280967827456
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98362871707890815223447806859131486208
                            128)
                          (Nat.shiftLeft
                            12427757432700032132770168832
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            12427757425638387915979489280
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            98364332041382580375173234718517755904
                            128)
                          (Nat.shiftLeft
                            340010386836983199563776
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          (Nat.shiftLeft
                            340157960719204131799040
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      255211775190703847597530955573826158592
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311922041479621234956341036481568047104
                          128)
                        256))
                    85070591730234615865843651857942052864)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32196112427976804180774879232
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6955809624473731072
                            32196112434932613806322352128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208)
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        256)
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          29710560942849126597578981376
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            29749246576032604355643310080
                            6955809625547472896)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            302231454974026037854208
                            70368744177664)
                          256)))))))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            302236066589675721064448)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            6917529027641081856
                            32196112435038448396491816960)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32196112427976804181848621056
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            302231454974026037854208)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            19807040633177770416813375488
                            4611686018427387904))
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        85071889804449249572750784482024357888
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          19807040628566084398385987584)
                        (Nat.shiftLeft
                          19807040628566084398385987584
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Code.joinWords 128
                            29710560949766655626293805056
                            7061644216790679552))
                        (Nat.shiftLeft
                          29749246569076794732243320832
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            302231454974026037854208
                            70368744177664))
                        (Nat.shiftLeft
                          302231454903657293676544
                          256))))))
              16384))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2240 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage035
