import Eliashberg

set_option pp.numericTypes true
set_option pp.coercions true
open Eliashberg

-- 主定理陈述的完整弹性化，检查数字字面量的类型与所有隐含实例。
#check @theorem_1_1_a
#check @theorem_1_1_b
#check @theorem_1_14
#check @corollary_1_17
#check @theorem_2_1
#check @theorem_2_1_strict
#check @theorem_2_1_iff
#check @theorem_2_3
#check @theorem_2_3_Tc
#check @corollary_2_4_i
#check @corollary_2_4_iii_Tc
#check @corollary_2_4_iii_Tec
#check @theorem_A10
#check @certA_g2
#check @certA'_g2
#check @certB_g2
#check @certD_g2
#check @Cinf_mem
#check @exists_cone_eigenvector_l2
#check @semigroup_preserves_cone
#check @theorem_1_8
#check @lemma_2_2_h_lt
#check @g2_hasEigenvalue
#check @Aop_isCompact
