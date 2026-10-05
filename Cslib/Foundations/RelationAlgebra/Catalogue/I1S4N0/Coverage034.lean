/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2177–2240 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage034

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59421121885698253195157962752
                            47288380205039616)
                          (Code.joinWords 128
                            909055547952406703636480
                            311922041479621234956341036481568047104))
                        512)
                      1024)
                    2048)
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071125300540235344749434731757568
                            2097152)
                          (Code.joinWords 128
                            59575864390608925729520353280
                            311922041479621234956341036481568047104))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            311043245305794506779468928881663148032
                            2097152)
                          (Code.joinWords 128
                            59575864390608925729520353280
                            311926108736572067230375738653802496000))
                        512))))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          45035996273704960
                          47287796087914496)
                        (Code.joinWords 128
                          909055547952406703636480
                          311922041479621234956341036481568096256))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          45036546029568128
                          47288380211331072)
                        2361183241434822606848)
                      512)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59459807511925921328748560384
                            41103477866897391940009984)
                          (Code.joinWords 128
                            9218855243087872
                            9227651336110080))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59459807511925921328748560384
                            2417851639229258349412352)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254740992))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59459807511925921328748560384
                            2417851639229258349412352)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254740992))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298415589417562316413461294878809915392
                            41539008693578735142944718985363456)
                          (Nat.shiftLeft
                            704520
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298415589417562316413461294878809915392
                            41539008693578735142944718985363456)
                          (Code.joinWords 128
                            9218855243087872
                            9227651336110080))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298415589417562316413461294878809915392
                            41539008693578735142944718985363456)
                          (Code.joinWords 128
                            9007199254740992
                            302231463910856548417536))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298411685053713613466904685032937357312
                            41538374868278621028243970633891840)
                          (Code.joinWords 128
                            9007199254740992
                            618970019651697336704434176))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            311707869375411475142499365481613361152
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254872064))
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
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          573440
                          128)
                        (Nat.shiftLeft
                          311922041479622144011889208790597290112
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            180232
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782173977334906880
                            128)
                          (Nat.shiftLeft
                            618970019651917788785672192
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735143507668938915840
                            128)
                          (Nat.shiftLeft
                            619916854131512700569649152
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472668036178936725504
                            128)
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782736927288328192
                            128)
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128))
                        512))))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687444453372461056
                        170141183460469231731687444453372461056)
                      256)
                    512)
                  1024)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          573440
                          128)
                        (Code.joinWords 128
                          298577838553186727951017872021704982528
                          311922041479622144011889246173992634496))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Code.joinWords 128
                            19807040628575303253629075456
                            9227651336110080))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374868278621028806920587313152
                            128)
                          (Code.joinWords 128
                            69479384704900975127968088064
                            618970019651697336704303104))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            41538374868278621028806920587182080
                            41539008693578735143507668938915840)
                          (Code.joinWords 128
                            19807342860029995254934405120
                            9007199254740992))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            180232
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782173977334906880
                            128)
                          (Code.joinWords 128
                            9218855243087872
                            9265034731454464))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735143507677528850432
                            128)
                          (Code.joinWords 128
                            302231463910856548417536
                            302231463910993987371008))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472668036178936725504
                            128)
                          (Code.joinWords 128
                            9007199254740992
                            618970019651697336704434176))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            41538374868278621028806920587182080
                            41539008695996586782736935878262784)
                          (Code.joinWords 128
                            9007199254740992
                            9007336693825536))
                        512))))))
            32768)))
      262144)
    (Code.joinWords 262144
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
                          9223372036854775808
                          9223372036854775808)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          170141183460469231731687303715884105728)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4611686018427387904
                          128)
                        19807040628566084398385987584)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4611686018427387904
                          128)
                        85070591730234615865843651857942052864)
                      1024)
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
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
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        19807040628566084398385987584)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        85070591730234615865843651857942052864)
                      1024)
                    2048)
                  4096))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
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
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13835058055282163712
                            128)
                          (Nat.shiftLeft
                            219902325555200
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3104559431276183267517136896
                            128)
                          (Nat.shiftLeft
                            311922041479621234956341036481568047104
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155547170143322817691648
                            128)
                          (Nat.shiftLeft
                            14411518807585587200
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33554432
                            128)
                          (Nat.shiftLeft
                            311922041479621234956341036481568047104
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298581732775830629088456631713972355072
                            128)
                          (Nat.shiftLeft
                            14411518807585587200
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33554432
                            128)
                          (Nat.shiftLeft
                            311926108736572067230375738653802496000
                            128))))))
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13979173243358019584
                            128)
                          (Nat.shiftLeft
                            619914492939264066492301312
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            144678138029277184
                            128)
                          (Nat.shiftLeft
                            619916854122505501314908160
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13979173243358019584
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953421312
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13979173243358019584
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953421312
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128)))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3094850098213450687247810560
                          128)
                        (Nat.shiftLeft
                          219902325555200
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3104521504770367720645984256
                          128)
                        (Nat.shiftLeft
                          311922041479621234956341036481568096256
                          128)))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3094887877145313644409571328
                          128)
                        (Nat.shiftLeft
                          8796093022208
                          128))
                      (Nat.shiftLeft
                        3104559431276183267617800192
                        128))
                    1024))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          308384951504021212847768027435297144832
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            704520
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308384951504021212847768027435297144832
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            618970019642760506193739776
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308384951504021212847768027435297144832
                            128)
                          (Nat.shiftLeft
                            619914492939264066492301312
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            619916854122505501314908160
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895022100482513683237985039941632
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374868278621028243970633891840
                            128)
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            309215719001386785268332906847972360192
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Nat.shiftLeft
                            618970019642690137449693184
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          13835058055282163712)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33554432
                            128)
                          (Code.joinWords 128
                            538968064
                            311922041479621234956341036482140569600)))
                      (Code.joinWords 128
                        85071889804449249572750784482024357888
                        4611686018427387904))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4611686018427387904
                          128)
                        (Code.joinWords 128
                          70368744177664
                          70368744177664))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            13835058055282163712
                            297747071055821155547170143322817691648)
                          (Code.joinWords 128
                            13835058055282163712
                            14449799404418236416))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33554432
                            128)
                          (Code.joinWords 128
                            298577838553186727951017660915472400384
                            311922041479621234956341036481568047104)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          4611686018427387904
                          85071889804449249577362540870269665280)
                        (Code.joinWords 128
                          4611686018427387904
                          4611686018427387904))))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13979173243358019584
                            128)
                          (Code.joinWords 128
                            69324642199981295394350956544
                            618970019642690137449562112))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            144678138029277184
                            128)
                          (Code.joinWords 128
                            69479384704891967928713347072
                            618970019642690137449562112)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          19807342860020988055679664128)
                        (Nat.shiftLeft
                          19807342860020988055679664128
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4611686018427387904
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16384
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4611686018427387904
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            70368744177664
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13979173243358019584
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953421312
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128)))
                      (Nat.shiftLeft
                        4611686018427387904
                        128))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          70368744177664
                          70368744177664)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16384
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        16384
                        16384)
                      70368744177664)
                    1024))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            85071889804449249572750784482024357888)
                          19807040628566084398385987584)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            69324642199981295394350956544
                            618970019642690137449562112))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69479384704900975127968088064
                            618970019651697336704303104)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            85071889804449249572750784482024357888)
                          19807342860020988055679664128)
                        (Nat.shiftLeft
                          19807342860020988055679664128
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          85071889804449249572750784482024357888)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16384
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          85071889804449249572750784482024374272
                          85071889804449249572750784482024357888)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024374272
                            85071889804449249572750784482024357888)
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591730234615865843651857942052864)
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            9007199254740992
                            618970019651697336704434176)))
                      (Code.joinWords 128
                        85071889804449249572750784482024374272
                        85071889804449249572750784482024357888)))))))))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        297747071055821155530452781502797185024
                        (Nat.shiftLeft
                          570425344
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          59421121885698253195157962752
                          2097152)
                        (Nat.shiftLeft
                          311922041479621234956341036482140569600
                          128)))
                    (Code.joinWords 512
                      85071889804449249572750784482024357888
                      19807040628566084398385987584))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            16717361816799281152)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59459807511925921328748560384
                            41103477866897391940009984)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254740992)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611756387171565568
                            4611756387171565568)
                          256)
                        19807040628566084398385987584))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            4611686018427387904
                            302236066589675721064448))
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            618970036360051954248843264)
                          256)
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Code.joinWords 128
                            9007199254740992
                            618970019651697336704303104)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            4611756387171565568
                            4611756387171565568))
                        85071889804449249572750784482024357888)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Code.joinWords 256
                          19807040628566084398385987584
                          302231454903657293676544))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          59421121885698253195157962752
                          (Code.joinWords 128
                            59421121885698253195157962752
                            311039351013670314259490852105600630784))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071125300540235344749434731757568
                            2097152)
                          (Code.joinWords 128
                            62061415875736603312716251136
                            311922041479621234956341036481568047104)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          19807040628566084398385987584
                          19807040628566084398385987584)
                        (Code.joinWords 256
                          85071889824256592432771772538777763840
                          19807040628566084398385987584)))
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          302231454903657293676544
                          16384)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        302231454903657293676544)
                      16384)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          19807040628566084398385987584
                          (Nat.shiftLeft
                            16384
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)
                        (Code.joinWords 256
                          19807040628566084398385987584
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          19807040628566084398385987584
                          (Nat.shiftLeft
                            302231454903657293676544
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59459807511925921328748560384
                            2417851639229258349412352)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254740992))
                        512)
                      (Nat.shiftLeft
                        19807040628566084398385987584
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        85071889804449249572750784482024357888
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Nat.shiftLeft
                            16384
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85071889804449249572750784482024374272
                          (Code.joinWords 128
                            70368744177664
                            70368744177664))
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85071889804449249572750784482024374272
                          (Nat.shiftLeft
                            302231454903657293676544
                            128))
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          (Nat.shiftLeft
                            302231454903657293676544
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            131072)
                          (Code.joinWords 128
                            618970019651697336704434176
                            618970019651697336704434176)))
                      (Code.joinWords 512
                        85071889804449249572750784482024374272
                        85071889804449249572750784482024357888)))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
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
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            619914497550950084919689216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            619916854122505501314908160
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            618970036360051954248843264
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472667473228983304192
                            128)
                          (Nat.shiftLeft
                            618970019651697336704303104
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472667473228983173120
                            128)
                          (Nat.shiftLeft
                            618970024254446524621127680
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996586782173977334906880
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128)))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          311039351013671220953855563077481709568
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          573440
                          128)
                        (Nat.shiftLeft
                          311922041479622295717912470977949780096
                          128)))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985363456
                            128)
                          (Nat.shiftLeft
                            180232
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            618970019642760506193739776
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996623675662124754010112
                            128)
                          (Nat.shiftLeft
                            618979464375726245484167168
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            619914492939264066492301312
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735143507668938915840
                            128)
                          (Nat.shiftLeft
                            620068560145767688667398144
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472668036178936725504
                            128)
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41538374870696472667473228983173120
                            128)
                          (Nat.shiftLeft
                            618970019642690137449562112
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008695996623676225074707431424
                            128)
                          (Nat.shiftLeft
                            618979464375655876740120576
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        42535295865117307932921825932729122816
                        (Code.joinWords 128
                          536870912
                          570425344))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          536870912
                          128)
                        (Code.joinWords 128
                          538968064
                          572522496)))
                    1298074214633706907132625156063232)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69324642216122196458846814208
                            618970036360051954248843264)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69479384704900975127968088064
                            618970019651697336704303104)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            19807342864632744442851229696
                            4611756387171565568))
                        (Nat.shiftLeft
                          19807342860020988055679664128
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16384
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            70368744177664
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            302236066589675721064448
                            302236066589675721064448))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            618970036398332551081492480)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2417851639229258349543424
                            128)
                          (Code.joinWords 128
                            9007199254740992
                            618970019651697336704303104)))
                      (Code.joinWords 256
                        16384
                        (Code.joinWords 128
                          4611756387171565568
                          4611756387171565568)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          302231454903657293692928
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          16384
                          128)
                        (Code.joinWords 128
                          70368744194048
                          302231454974026037870592)))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          131072
                          128)
                        512)
                      16384)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            16384)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154767130165248
                            70368744177664)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69324642199981295394350956544
                            618970019642690137449562112)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            562949953552384
                            128)
                          (Code.joinWords 128
                            71964936190028652711163985920
                            618970019651697336704303104)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          19807342860020988055679664128)
                        (Nat.shiftLeft
                          19807342860020988055679664128
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16384
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            70368744177664
                            70368744177664))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            302231454903657293676544
                            302231454903657293676544)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            618970019651697336704434176
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2417851639792208302964736
                            128)
                          (Code.joinWords 128
                            618970019651697336704434176
                            618970019651697336704434176)))
                      16384))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2176 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage034
