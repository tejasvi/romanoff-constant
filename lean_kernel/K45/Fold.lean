import RCert.Data45
import K45.Assembly
import K45.S.SOpts
import K45.S.SSmall
import K45.S.S8M
import K45.S.SL9M
import K45.S.S8_000
import K45.S.S8_001
import K45.S.S8_002
import K45.S.S8_003
import K45.S.S8_004
import K45.S.S8_005
import K45.S.S9_000
import K45.S.S9_001
import K45.S.S9_002
import K45.S.S9_003
import K45.S.S9_004
import K45.S.S9_005
import K45.S.S9_006
import K45.S.S9_007
import K45.S.S9_008
import K45.S.S9_009
import K45.S.S9_010
import K45.S.S9_011
import K45.S.S9_012
import K45.S.S9_013
import K45.S.S9_014
import K45.S.S9_015
import K45.S.S9_016
import K45.S.S9_017
import K45.S.S9_018
import K45.S.S9_019
import K45.S.S9_020
import K45.S.S9_021
import K45.S.S9_022
import K45.S.S9_023
import K45.S.S9_024
import K45.S.S9_025
import K45.S.S9_026
import K45.S.S9_027
import K45.S.S9_028
import K45.S.S9_029
import K45.S.S9_030
import K45.S.S9_031
import K45.S.S9_032
import K45.S.S9_033
import K45.S.S9_034
import K45.S.S9_035
import K45.S.S9_036
import K45.S.S9_037
import K45.S.S9_038
import K45.S.S9_039
import K45.S.S9_040
import K45.S.S9_041
import K45.S.S9_042
import K45.S.S9_043
import K45.S.S9_044
import K45.S.S9_045
import K45.S.S9_046
import K45.S.S9_047
import K45.S.S9_048
import K45.S.S9_049
import K45.S.S9_050
import K45.S.S9_051
import K45.S.S9_052
import K45.S.S9_053
import K45.S.S9_054
import K45.S.S9_055
import K45.S.SM9_000
import K45.S.SM9_001
import K45.S.SM9_002
import K45.S.SM9_003
import K45.S.SM9_004
import K45.S.SM9_005
import K45.S.SM9_006
import K45.S.SM9_007
import K45.S.SM9_008
import K45.S.SM9_009
import K45.S.SM9_010
import K45.S.SM9_011
import K45.S.SM9_012
import K45.S.SM9_013
import K45.S.SOC_000
import K45.S.SOC_001
import K45.S.SOC_002
import K45.S.SOC_003
import K45.S.SOC_004
import K45.S.SOC_005
import K45.S.SOC_006
import K45.S.SOC_007
import K45.S.SOC_008
import K45.S.SOC_009
import K45.S.SOC_010
import K45.S.SOC_011
import K45.S.SOC_012
import K45.S.SOC_013
import K45.S.SOC_014
import K45.S.SOC_015
import K45.S.SOC_016
import K45.S.SOC_017
import K45.S.SOC_018
import K45.S.SOC_019
import K45.S.SOC_020
import K45.S.SOC_021
import K45.S.SOC_022
import K45.S.SOC_023
import K45.S.SOC_024
import K45.S.SOC_025
import K45.S.SOC_026
import K45.S.SOC_027
import K45.S.SOC_028
import K45.S.SOC_029
import K45.S.SOC_030
import K45.S.SOC_031
import K45.S.SOC_032
import K45.S.SOC_033
import K45.S.SOC_034
import K45.S.SOC_035
import K45.S.SOC_036
import K45.S.SOC_037
import K45.S.SOC_038
import K45.S.SOC_039
import K45.S.SOC_040
import K45.S.SOC_041
import K45.S.SOC_042
import K45.S.SOC_043
import K45.S.SOC_044
import K45.S.SOC_045
import K45.S.SOC_046
import K45.S.SOC_047
import K45.S.SOC_048
import K45.S.SOC_049
import K45.S.SOC_050
import K45.S.SOC_051
import K45.S.SOC_052
import K45.S.SOC_053
import K45.S.SOC_054
import K45.S.SOC_055
import K45.S.SOC_056
import K45.S.SOC_057
import K45.S.SOC_058
import K45.S.SOC_059
import K45.S.SOC_060
import K45.S.SOC_061
import K45.S.SOC_062
import K45.S.SOC_063
import K45.S.SOC_064
import K45.S.SOC_065
import K45.S.SOC_066
import K45.S.SOC_067
import K45.S.SOC_068
import K45.S.SOC_069
import K45.S.SOC_070
import K45.S.SOC_071
import K45.S.SOC_072
import K45.S.SOC_073
import K45.S.SOC_074
import K45.S.SOC_075
import K45.S.SOC_076
import K45.S.SOC_077
import K45.S.SOC_078
import K45.S.SOC_079
import K45.S.SOC_080
import K45.S.SOC_081
import K45.S.SOC_082
import K45.S.SOC_083
import K45.S.SOC_084
import K45.S.SOC_085
import K45.S.SOC_086
import K45.S.SOC_087
import K45.S.SOC_088
import K45.S.SOC_089
import K45.S.SOC_090
import K45.S.SOC_091
import K45.S.SOC_092
import K45.G.B9All
import K45.G.M9All
import K45.Orb.OAll

set_option maxRecDepth 100000

/-! The fold of the 45a certificate, kernel-checked: `foldOrbits 120 ps = L9` and `orbits 120 ps = orbLit`. -/

namespace K45

open R45 R45.D45 Romanoff K45.G

theorem step1 : foldStep 120 [(0, 1)] (optsP 120 3) = L1 := by
  rw [S.opts3_eq]
  exact step_of_normK (by decide) S.opts3_pos S.s1 S.p1

theorem step2 : foldStep 120 L1 (optsP 120 5) = L2 := by
  rw [S.opts5_eq]
  exact step_of_normK (strictPos_spec _ S.p1).2 S.opts5_pos S.s2 S.p2

theorem step3 : foldStep 120 L2 (optsP 120 7) = L3 := by
  rw [S.opts7_eq]
  exact step_of_normK (strictPos_spec _ S.p2).2 S.opts7_pos S.s3 S.p3

theorem step4 : foldStep 120 L3 (optsP 120 11) = L4 := by
  rw [S.opts11_eq]
  exact step_of_normK (strictPos_spec _ S.p3).2 S.opts11_pos S.s4 S.p4

theorem step5 : foldStep 120 L4 (optsP 120 13) = L5 := by
  rw [S.opts13_eq]
  exact step_of_normK (strictPos_spec _ S.p4).2 S.opts13_pos S.s5 S.p5

theorem step6 : foldStep 120 L5 (optsP 120 17) = L6 := by
  rw [S.opts17_eq]
  exact step_of_normK (strictPos_spec _ S.p5).2 S.opts17_pos S.s6 S.p6

theorem step7 : foldStep 120 L6 (optsP 120 31) = L7 := by
  rw [S.opts31_eq]
  exact step_of_normK (strictPos_spec _ S.p6).2 S.opts31_pos S.s7 S.p7

theorem step8 : foldStep 120 L7 (optsP 120 41) = L8 := by
  rw [S.opts41_eq]
  have hB : List.Forall₂ (fun C B => normK (prodK 120 C opts41) = B) L7chunks B8s :=
    .cons S.s8_000 (.cons S.s8_001 (.cons S.s8_002 (.cons S.s8_003 (.cons S.s8_004 (.cons S.s8_005 (.cons S.s8_006 (.cons S.s8_007 (.cons S.s8_008 (.cons S.s8_009 (.cons S.s8_010 (.cons S.s8_011 (.cons S.s8_012 (.cons S.s8_013 (.cons S.s8_014 (.cons S.s8_015 (.cons S.s8_016 (.cons S.s8_017 (.nil))))))))))))))))))
  exact step_exact (strictPos_spec _ S.p7).2 S.opts41_pos (step_check hB S.m8) S.p8

theorem step9 : foldStep 120 L8 (optsP 120 241) = L9 := by
  rw [S.opts241_eq]
  have hB : List.Forall₂ (fun C B => normK (prodK 120 C opts241) = B) L8chunks B9s :=
    .cons S.s9_000 (.cons S.s9_001 (.cons S.s9_002 (.cons S.s9_003 (.cons S.s9_004 (.cons S.s9_005 (.cons S.s9_006 (.cons S.s9_007 (.cons S.s9_008 (.cons S.s9_009 (.cons S.s9_010 (.cons S.s9_011 (.cons S.s9_012 (.cons S.s9_013 (.cons S.s9_014 (.cons S.s9_015 (.cons S.s9_016 (.cons S.s9_017 (.cons S.s9_018 (.cons S.s9_019 (.cons S.s9_020 (.cons S.s9_021 (.cons S.s9_022 (.cons S.s9_023 (.cons S.s9_024 (.cons S.s9_025 (.cons S.s9_026 (.cons S.s9_027 (.cons S.s9_028 (.cons S.s9_029 (.cons S.s9_030 (.cons S.s9_031 (.cons S.s9_032 (.cons S.s9_033 (.cons S.s9_034 (.cons S.s9_035 (.cons S.s9_036 (.cons S.s9_037 (.cons S.s9_038 (.cons S.s9_039 (.cons S.s9_040 (.cons S.s9_041 (.cons S.s9_042 (.cons S.s9_043 (.cons S.s9_044 (.cons S.s9_045 (.cons S.s9_046 (.cons S.s9_047 (.cons S.s9_048 (.cons S.s9_049 (.cons S.s9_050 (.cons S.s9_051 (.cons S.s9_052 (.cons S.s9_053 (.cons S.s9_054 (.cons S.s9_055 (.cons S.s9_056 (.cons S.s9_057 (.cons S.s9_058 (.cons S.s9_059 (.cons S.s9_060 (.cons S.s9_061 (.cons S.s9_062 (.cons S.s9_063 (.cons S.s9_064 (.cons S.s9_065 (.cons S.s9_066 (.cons S.s9_067 (.cons S.s9_068 (.cons S.s9_069 (.cons S.s9_070 (.cons S.s9_071 (.cons S.s9_072 (.cons S.s9_073 (.cons S.s9_074 (.cons S.s9_075 (.cons S.s9_076 (.cons S.s9_077 (.cons S.s9_078 (.cons S.s9_079 (.cons S.s9_080 (.cons S.s9_081 (.cons S.s9_082 (.cons S.s9_083 (.cons S.s9_084 (.cons S.s9_085 (.cons S.s9_086 (.cons S.s9_087 (.cons S.s9_088 (.cons S.s9_089 (.cons S.s9_090 (.cons S.s9_091 (.cons S.s9_092 (.cons S.s9_093 (.cons S.s9_094 (.cons S.s9_095 (.cons S.s9_096 (.cons S.s9_097 (.cons S.s9_098 (.cons S.s9_099 (.cons S.s9_100 (.cons S.s9_101 (.cons S.s9_102 (.cons S.s9_103 (.cons S.s9_104 (.cons S.s9_105 (.cons S.s9_106 (.cons S.s9_107 (.cons S.s9_108 (.cons S.s9_109 (.cons S.s9_110 (.cons S.s9_111 (.cons S.s9_112 (.cons S.s9_113 (.cons S.s9_114 (.cons S.s9_115 (.cons S.s9_116 (.cons S.s9_117 (.cons S.s9_118 (.cons S.s9_119 (.cons S.s9_120 (.cons S.s9_121 (.cons S.s9_122 (.cons S.s9_123 (.cons S.s9_124 (.cons S.s9_125 (.cons S.s9_126 (.cons S.s9_127 (.cons S.s9_128 (.cons S.s9_129 (.cons S.s9_130 (.cons S.s9_131 (.cons S.s9_132 (.cons S.s9_133 (.cons S.s9_134 (.cons S.s9_135 (.cons S.s9_136 (.cons S.s9_137 (.cons S.s9_138 (.cons S.s9_139 (.cons S.s9_140 (.cons S.s9_141 (.cons S.s9_142 (.cons S.s9_143 (.cons S.s9_144 (.cons S.s9_145 (.cons S.s9_146 (.cons S.s9_147 (.cons S.s9_148 (.cons S.s9_149 (.cons S.s9_150 (.cons S.s9_151 (.cons S.s9_152 (.cons S.s9_153 (.cons S.s9_154 (.cons S.s9_155 (.cons S.s9_156 (.cons S.s9_157 (.cons S.s9_158 (.cons S.s9_159 (.cons S.s9_160 (.cons S.s9_161 (.cons S.s9_162 (.cons S.s9_163 (.cons S.s9_164 (.cons S.s9_165 (.cons S.s9_166 (.cons S.s9_167 (.cons S.s9_168 (.cons S.s9_169 (.cons S.s9_170 (.cons S.s9_171 (.cons S.s9_172 (.cons S.s9_173 (.cons S.s9_174 (.cons S.s9_175 (.cons S.s9_176 (.cons S.s9_177 (.cons S.s9_178 (.cons S.s9_179 (.cons S.s9_180 (.cons S.s9_181 (.cons S.s9_182 (.cons S.s9_183 (.cons S.s9_184 (.cons S.s9_185 (.cons S.s9_186 (.cons S.s9_187 (.cons S.s9_188 (.cons S.s9_189 (.cons S.s9_190 (.cons S.s9_191 (.cons S.s9_192 (.cons S.s9_193 (.cons S.s9_194 (.cons S.s9_195 (.cons S.s9_196 (.cons S.s9_197 (.cons S.s9_198 (.cons S.s9_199 (.cons S.s9_200 (.cons S.s9_201 (.cons S.s9_202 (.cons S.s9_203 (.cons S.s9_204 (.cons S.s9_205 (.cons S.s9_206 (.cons S.s9_207 (.cons S.s9_208 (.cons S.s9_209 (.cons S.s9_210 (.cons S.s9_211 (.cons S.s9_212 (.cons S.s9_213 (.cons S.s9_214 (.cons S.s9_215 (.cons S.s9_216 (.cons S.s9_217 (.cons S.s9_218 (.cons S.s9_219 (.cons S.s9_220 (.cons S.s9_221 (.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have hG : List.Forall₂ (fun G M => mergeRuns G = M) B9groups M9s :=
    .cons S.m9_000 (.cons S.m9_001 (.cons S.m9_002 (.cons S.m9_003 (.cons S.m9_004 (.cons S.m9_005 (.cons S.m9_006 (.cons S.m9_007 (.cons S.m9_008 (.cons S.m9_009 (.cons S.m9_010 (.cons S.m9_011 (.cons S.m9_012 (.cons S.m9_013 (.nil))))))))))))))
  exact step_exact (strictPos_spec _ S.p8).2 S.opts241_pos (step_check2 hB hG rfl S.m9all) S.p9

theorem fold_eq : foldOrbits 120 (ellPO.map (·.1)) = L9 := by
  show foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120 (foldStep 120
    (foldStep 120 (foldStep 120 [(0, 1)] (optsP 120 3)) (optsP 120 5)) (optsP 120 7)) (optsP 120 11))
    (optsP 120 13)) (optsP 120 17)) (optsP 120 31)) (optsP 120 41)) (optsP 120 241) = L9
  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9]

theorem orbits_eq : orbits 120 (ellPO.map (·.1)) = K45.Orb.orbLit := by
  rw [orbits_eq_filterMap, fold_eq]
  have hOC : List.Forall₂ (fun c o => c.filterMap orbF = o) L9chunks K45.Orb.orbChunks :=
    .cons S.oc_000 (.cons S.oc_001 (.cons S.oc_002 (.cons S.oc_003 (.cons S.oc_004 (.cons S.oc_005 (.cons S.oc_006 (.cons S.oc_007 (.cons S.oc_008 (.cons S.oc_009 (.cons S.oc_010 (.cons S.oc_011 (.cons S.oc_012 (.cons S.oc_013 (.cons S.oc_014 (.cons S.oc_015 (.cons S.oc_016 (.cons S.oc_017 (.cons S.oc_018 (.cons S.oc_019 (.cons S.oc_020 (.cons S.oc_021 (.cons S.oc_022 (.cons S.oc_023 (.cons S.oc_024 (.cons S.oc_025 (.cons S.oc_026 (.cons S.oc_027 (.cons S.oc_028 (.cons S.oc_029 (.cons S.oc_030 (.cons S.oc_031 (.cons S.oc_032 (.cons S.oc_033 (.cons S.oc_034 (.cons S.oc_035 (.cons S.oc_036 (.cons S.oc_037 (.cons S.oc_038 (.cons S.oc_039 (.cons S.oc_040 (.cons S.oc_041 (.cons S.oc_042 (.cons S.oc_043 (.cons S.oc_044 (.cons S.oc_045 (.cons S.oc_046 (.cons S.oc_047 (.cons S.oc_048 (.cons S.oc_049 (.cons S.oc_050 (.cons S.oc_051 (.cons S.oc_052 (.cons S.oc_053 (.cons S.oc_054 (.cons S.oc_055 (.cons S.oc_056 (.cons S.oc_057 (.cons S.oc_058 (.cons S.oc_059 (.cons S.oc_060 (.cons S.oc_061 (.cons S.oc_062 (.cons S.oc_063 (.cons S.oc_064 (.cons S.oc_065 (.cons S.oc_066 (.cons S.oc_067 (.cons S.oc_068 (.cons S.oc_069 (.cons S.oc_070 (.cons S.oc_071 (.cons S.oc_072 (.cons S.oc_073 (.cons S.oc_074 (.cons S.oc_075 (.cons S.oc_076 (.cons S.oc_077 (.cons S.oc_078 (.cons S.oc_079 (.cons S.oc_080 (.cons S.oc_081 (.cons S.oc_082 (.cons S.oc_083 (.cons S.oc_084 (.cons S.oc_085 (.cons S.oc_086 (.cons S.oc_087 (.cons S.oc_088 (.cons S.oc_089 (.cons S.oc_090 (.cons S.oc_091 (.cons S.oc_092 (.cons S.oc_093 (.cons S.oc_094 (.cons S.oc_095 (.cons S.oc_096 (.cons S.oc_097 (.cons S.oc_098 (.cons S.oc_099 (.cons S.oc_100 (.cons S.oc_101 (.cons S.oc_102 (.cons S.oc_103 (.cons S.oc_104 (.cons S.oc_105 (.cons S.oc_106 (.cons S.oc_107 (.cons S.oc_108 (.cons S.oc_109 (.cons S.oc_110 (.cons S.oc_111 (.cons S.oc_112 (.cons S.oc_113 (.cons S.oc_114 (.cons S.oc_115 (.cons S.oc_116 (.cons S.oc_117 (.cons S.oc_118 (.cons S.oc_119 (.cons S.oc_120 (.cons S.oc_121 (.cons S.oc_122 (.cons S.oc_123 (.cons S.oc_124 (.cons S.oc_125 (.cons S.oc_126 (.cons S.oc_127 (.cons S.oc_128 (.cons S.oc_129 (.cons S.oc_130 (.cons S.oc_131 (.cons S.oc_132 (.cons S.oc_133 (.cons S.oc_134 (.cons S.oc_135 (.cons S.oc_136 (.cons S.oc_137 (.cons S.oc_138 (.cons S.oc_139 (.cons S.oc_140 (.cons S.oc_141 (.cons S.oc_142 (.cons S.oc_143 (.cons S.oc_144 (.cons S.oc_145 (.cons S.oc_146 (.cons S.oc_147 (.cons S.oc_148 (.cons S.oc_149 (.cons S.oc_150 (.cons S.oc_151 (.cons S.oc_152 (.cons S.oc_153 (.cons S.oc_154 (.cons S.oc_155 (.cons S.oc_156 (.cons S.oc_157 (.cons S.oc_158 (.cons S.oc_159 (.cons S.oc_160 (.cons S.oc_161 (.cons S.oc_162 (.cons S.oc_163 (.cons S.oc_164 (.cons S.oc_165 (.cons S.oc_166 (.cons S.oc_167 (.cons S.oc_168 (.cons S.oc_169 (.cons S.oc_170 (.cons S.oc_171 (.cons S.oc_172 (.cons S.oc_173 (.cons S.oc_174 (.cons S.oc_175 (.cons S.oc_176 (.cons S.oc_177 (.cons S.oc_178 (.cons S.oc_179 (.cons S.oc_180 (.cons S.oc_181 (.cons S.oc_182 (.cons S.oc_183 (.cons S.oc_184 (.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  show L9chunks.flatten.filterMap orbF = K45.Orb.orbChunks.flatten
  rw [filterMap_flatten, map_filterMap_of_forall₂ hOC]

end K45
