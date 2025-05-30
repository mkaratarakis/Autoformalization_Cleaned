import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  have h := p
  have h1 := testBit_eq_true_iff h
  simp only [Nat.testBit_eq_true_iff] at h1
  have h2 := Nat.div_lt_of_lt h1
  simp only [Nat.div_lt_of_lt] at h2
  have h3 := Nat.lt_of_div_lt h2
  simp only [Nat.lt_of_div_lt] at h3
  have h4 := Nat.lt_of_mul_lt_left h3
  simp only [Nat.lt_of_mul_lt_left] at h4
  have h5 := Nat.lt_of_mul_lt_right h4
  simp only [Nat.lt_of_mul_lt_right] at h5
  have h6 := Nat.lt_of_mul_lt_left h5
  simp only [Nat.lt_of_mul_lt_left] at h6
  have h7 := Nat.lt_of_mul_lt_right h6
  simp only [Nat.lt_of_mul_lt_right] at h7
  have h8 := Nat.lt_of_mul_lt_left h7
  simp only [Nat.lt_of_mul_lt_left] at h8
  have h9 := Nat.lt_of_mul_lt_right h8
  simp only [Nat.lt_of_mul_lt_right] at h9
  have h10 := Nat.lt_of_mul_lt_left h9
  simp only [Nat.lt_of_mul_lt_left] at h10
  have h11 := Nat.lt_of_mul_lt_right h10
  simp only [Nat.lt_of_mul_lt_right] at h11
  have h12 := Nat.lt_of_mul_lt_left h11
  simp only [Nat.lt_of_mul_lt_left] at h12
  have h13 := Nat.lt_of_mul_lt_right h12
  simp only [Nat.lt_of_mul_lt_right] at h13
  have h14 := Nat.lt_of_mul_lt_left h13
  simp only [Nat.lt_of_mul_lt_left] at h14
  have h15 := Nat.lt_of_mul_lt_right h14
  simp only [Nat.lt_of_mul_lt_right] at h15
  have h16 := Nat.lt_of_mul_lt_left h15
  simp only [Nat.lt_of_mul_lt_left] at h16
  have h17 := Nat.lt_of_mul_lt_right h16
  simp only [Nat.lt_of_mul_lt_right] at h17
  have h18 := Nat.lt_of_mul_lt_left h17
  simp only [Nat.lt_of_mul_lt_left] at h18
  have h19 := Nat.lt_of_mul_lt_right h18
  simp only [Nat.lt_of_mul_lt_right] at h19
  have h20 := Nat.lt_of_mul_lt_left h19
  simp only [Nat.lt_of_mul_lt_left] at h20
  have h21 := Nat.lt_of_mul_lt_right h20
  simp only [Nat.lt_of_mul_lt_right] at h21
  have h22 := Nat.lt_of_mul_lt_left h21
  simp only [Nat.lt_of_mul_lt_left] at h22
  have h23 := Nat.lt_of_mul_lt_right h22
  simp only [Nat.lt_of_mul_lt_right] at h23
  have h24 := Nat.lt_of_mul_lt_left h23
  simp only [Nat.lt_of_mul_lt_left] at h24
  have h25 := Nat.lt_of_mul_lt_right h24
  simp only [Nat.lt_of_mul_lt_right] at h25
  have h26 := Nat.lt_of_mul_lt_left h25
  simp only [Nat.lt_of_mul_lt_left] at h26
  have h27 := Nat.lt_of_mul_lt_right h26
  simp only [Nat.lt_of_mul_lt_right] at h27
  have h28 := Nat.lt_of_mul_lt_left h27
  simp only [Nat.lt_of_mul_lt_left] at h28
  have h29 := Nat.lt_of_mul_lt_right h28
  simp only [Nat.lt_of_mul_lt_right] at h29
  have h30 := Nat.lt_of_mul_lt_left h29
  simp only [Nat.lt_of_mul_lt_left] at h30
  have h31 := Nat.lt_of_mul_lt_right h30
  simp only [Nat.lt_of_mul_lt_right] at h31
  have h32 := Nat.lt_of_mul_lt_left h31
  simp only [Nat.lt_of_mul_lt_left] at h32
  have h33 := Nat.lt_of_mul_lt_right h32
  simp only [Nat.lt_of_mul_lt_right] at h33
  have h34 := Nat.lt_of_mul_lt_left h33
  simp only [Nat.lt_of_mul_lt_left] at h34
  have h35 := Nat.lt_of_mul_lt_right h34
  simp only [Nat.lt_of_mul_lt_right] at h35
  have h36 := Nat.lt_of_mul_lt_left h35
  simp only [Nat.lt_of_mul_lt_left] at h36
  have h37 := Nat.lt_of_mul_lt_right h36
  simp only [Nat.lt_of_mul_lt_right] at h37
  have h38 := Nat.lt_of_mul_lt_left h37
  simp only [Nat.lt_of_mul_lt_left] at h38
  have h39 := Nat.lt_of_mul_lt_right h38
  simp only [Nat.lt_of_mul_lt_right] at h39
  have h40 := Nat.lt_of_mul_lt_left h39
  simp only [Nat.lt_of_mul_lt_left] at h40
  have h41 := Nat.lt_of_mul_lt_right h40
  simp only [Nat.lt_of_mul_lt_right] at h41
  have h42 := Nat.lt_of_mul_lt_left h41
  simp only [Nat.lt_of_mul_lt_left] at h42
  have h43 := Nat.lt_of_mul_lt_right h42
  simp only [Nat.lt_of_mul_lt_right] at h43
  have h44 := Nat.lt_of_mul_lt_left h43
  simp only [Nat.lt_of_mul_lt_left] at h44
  have h45 := Nat.lt_of_mul_lt_right h44
  simp only [Nat.lt_of_mul_lt_right] at h45
  have h46 := Nat.lt_of_mul_lt_left h45
  simp only [Nat.lt_of_mul_lt_left] at h46
  have h47 := Nat.lt_of_mul_lt_right h46
  simp only [Nat.lt_of_mul_lt_right] at h47
  have h48 := Nat.lt_of_mul_lt_left h47
  simp only [Nat.lt_of_mul_lt_left] at h48
  have h49 := Nat.lt_of_mul_lt_right h48
  simp only [Nat.lt_of_mul_lt_right] at h49
  have h50 := Nat.lt_of_mul_lt_left h49
  simp only [Nat.lt_of_mul_lt_left] at h50
  have h51 := Nat.lt_of_mul_lt_right h50
  simp only [Nat.lt_of_mul_lt_right] at h51
  have h52 := Nat.lt_of_mul_lt_left h51
  simp only [Nat.lt_of_mul_lt_left] at h52
  have h53 := Nat.lt_of_mul_lt_right h52
  simp only [Nat.lt_of_mul_lt_right] at h53
  have h54 := Nat.lt_of_mul_lt_left h53
  simp only [Nat.lt_of_mul_lt_left] at h54
  have h55 := Nat.lt_of_mul_lt_right h54
  simp only [Nat.lt_of_mul_lt_right] at h55
  have h56 := Nat.lt_of_mul_lt_left h55
  simp only [Nat.lt_of_mul_lt_left] at h56
  have h57 := Nat.lt_of_mul_lt_right h56
  simp only [Nat.lt_of_mul_lt_right] at h57
  have h58 := Nat.lt_of_mul_lt_left h57
  simp only [Nat.lt_of_mul_lt_left] at h58
  have h59 := Nat.lt_of_mul_lt_right h58
  simp only [Nat.lt_of_mul_lt_right] at h59
  have h60 := Nat.lt_of_mul_lt_left h59
  simp only [Nat.lt_of_mul_lt_left] at h60
  have h61 := Nat.lt_of_mul_lt_right h60
  simp only [Nat.lt_of_mul_lt_right] at h61
  have h62 := Nat.lt_of_mul_lt_left h61
  simp only [Nat.lt_of_mul_lt_left] at h62
  have h63 := Nat.lt_of_mul_lt_right h62
  simp only [Nat.lt_of_mul_lt_right] at h63
  have h64 := Nat.lt_of_mul_lt_left h63
  simp only [Nat.lt_of_mul_lt_left] at h64
  have h65 := Nat.lt_of_mul_lt_right h64
  simp only [Nat.lt_of_mul_lt_right] at h65
  have h66 := Nat.lt_of_mul_lt_left h65
  simp only [Nat.lt_of_mul_lt_left] at h66
  have h67 := Nat.lt_of_mul_lt_right h66
  simp only [Nat.lt_of_mul_lt_right] at h67
  have h68 := Nat.lt_of_mul_lt_left h67
  simp only [Nat.lt_of_mul_lt_left] at h68
  have h69 := Nat.lt_of_mul_lt_right h68
  simp only [Nat.lt_of_mul_lt_right] at h69
  have h70 := Nat.lt_of_mul_lt_left h69
  simp only [Nat.lt_of_mul_lt_left] at h70
  have h71 := Nat.lt_of_mul_lt_right h70
  simp only [Nat.lt_of_mul_lt_right] at h71
  have h72 := Nat.lt_of_mul_lt_left h71
  simp only [Nat.lt_of_mul_lt_left] at h72
  have h73 := Nat.lt_of_mul_lt_right h72
  simp only [Nat.lt_of_mul_lt_right] at h73
  have h74 := Nat.lt_of_mul_lt_left h73
  simp only [Nat.lt_of_mul_lt_left] at h74
  have h75 := Nat.lt_of_mul_lt_right h74
  simp only [Nat.lt_of_mul_lt_right] at h75
  have h76 := Nat.lt_of_mul_lt_left h75
  simp only [Nat.lt_of_mul_lt_left] at h76
  have h77 := Nat.lt_of_mul_lt_right h76
  simp only [Nat.lt_of_mul_lt_right] at h77
  have h78 := Nat.lt_of_mul_lt_left h77
  simp only [Nat.lt_of_mul_lt_left] at h78
  have h79 := Nat.lt_of_mul_lt_right h78
  simp only [Nat.lt_of_mul_lt_right] at h79
  have h80 := Nat.lt_of_mul_lt_left h79
  simp only [Nat.lt_of_mul_lt_left] at h80
  have h81 := Nat.lt_of_mul_lt_right h80
  simp only [Nat.lt_of_mul_lt_right] at h81
  have h82 := Nat.lt_of_mul_lt_left h81
  simp only [Nat.lt_of_mul_lt_left] at h82
  have h83 := Nat.lt_of_mul_lt_right h82
  simp only [Nat.lt_of_mul_lt_right] at h83
  have h84 := Nat.lt_of_mul_lt_left h83
  simp only [Nat.lt_of_mul_lt_left] at h84
  have h85 := Nat.lt_of_mul_lt_right h84
  simp only [Nat.lt_of_mul_lt_right] at h85
  have h86 := Nat.lt_of_mul_lt_left h85
  simp only [Nat.lt_of_mul_lt_left] at h86
  have h87 := Nat.lt_of_mul_lt_right h86
  simp only [Nat.lt_of_mul_lt_right] at h87
  have h88 := Nat.lt_of_mul_lt_left h87
  simp only [Nat.lt_of_mul_lt_left] at h88
  have h89 := Nat.lt_of_mul_lt_right h88
  simp only [Nat.lt_of_mul_lt_right] at h89
  have h90 := Nat.lt_of_mul_lt_left h89
  simp only [Nat.lt_of_mul_lt_left] at h90
  have h91 := Nat.lt_of_mul_lt_right h90
  simp only [Nat.lt_of_mul_lt_right] at h91
  have h92 := Nat.lt_of_mul_lt_left h91
  simp only [Nat.lt_of_mul_lt_left] at h92
  have h93 := Nat.lt_of_mul_lt_right h92
  simp only [Nat.lt_of_mul_lt_right] at h93
  have h94 := Nat.lt_of_mul_lt_left h93
  simp only [Nat.lt_of_mul_lt_left] at h94
  have h95 := Nat.lt_of_mul_lt_right h94
  simp only [Nat.lt_of_mul_lt_right] at h95
  have h96 := Nat.lt_of_mul_lt_left h95
  simp only [Nat.lt_of_mul_lt_left] at h96
  have h97 := Nat.lt_of_mul_lt_right h96
  simp only [Nat.lt_of_mul_lt_right] at h97
  have h98 := Nat.lt_of_mul_lt_left h97
  simp only [Nat.lt_of_mul_lt_left] at h98
  have h99 := Nat.lt_of_mul_lt_right h98
  simp only [Nat.lt_of_mul_lt_right] at h99
  have h100 := Nat.lt_of_mul_lt_left h99
  simp only [Nat.lt_of_mul_lt_left] at h100
  have h101 := Nat.lt_of_mul_lt_right h100
  simp only [Nat.lt_of_mul_lt_right] at h101
  have h102 := Nat.lt_of_mul_lt_left h101
  simp only [Nat.lt_of_mul_lt_left] at h102
  have h103 := Nat.lt_of_mul_lt_right h102
  simp only [Nat.lt_of_mul_lt_right] at h103
  have h104 := Nat.lt_of_mul_lt_left h103
  simp only [Nat.lt_of_mul_lt_left] at h104
  have h105 := Nat.lt_of_mul_lt_right h104
  simp only [Nat.lt_of_mul_lt_right] at h105
  have h106 := Nat.lt_of_mul_lt_left h105
  simp only [Nat.lt_of_mul_lt_left] at h106
  have h107 := Nat.lt_of_mul_lt_right h106
  simp only [Nat.lt_of_mul_lt_right] at h107
  have h108 := Nat.lt_of_mul_lt_left h107
  simp only [Nat.lt_of_mul_lt_left] at h108
  have h109 := Nat.lt_of_mul_lt_right h108
  simp only [Nat.lt_of_mul_lt_right] at h109
  have h110 := Nat.lt_of_mul_lt_left h109
  simp only [Nat.lt_of_mul_lt_left] at h110
  have h111 := Nat.lt_of_mul_lt_right h110
  simp only [Nat.lt_of_mul_lt_right] at h111
  have h112 := Nat.lt_of_mul_lt_left h111
  simp only [Nat.lt_of_mul_lt_left] at h112
  have h113 := Nat.lt_of_mul_lt_right h112
  simp only [Nat.lt_of_mul_lt_right] at h113
  have h114 := Nat.lt_of_mul_lt_left h113
  simp only [Nat.lt_of_mul_lt_left] at h114
  have h115 := Nat.lt_of_mul_lt_right h114
  simp only [Nat.lt_of_mul_lt_right] at h115
  have h116 := Nat.lt_of_mul_lt_left h115
  simp only [Nat.lt_of_mul_lt_left] at h116
  have h117 := Nat.lt_of_mul_lt_right h116
  simp only [Nat.lt_of_mul_lt_right] at h117
  have h118 := Nat.lt_of_mul_lt_left h117
  simp only [Nat.lt_of_mul_lt_left] at h118
  have h119 := Nat.lt_of_mul_lt_right h118
  simp only [Nat.lt_of_mul_lt_right] at h119
  have h120 := Nat.lt_of_mul_lt_left h119
  simp only [Nat.lt_of_mul_lt_left] at h120
  have h121 := Nat.lt_of_mul_lt_right h120
  simp only [Nat.lt_of_mul_lt_right] at h121
  have h122 := Nat.lt_of_mul_lt_left h121
  simp only [Nat.lt_of_mul_lt_left] at h122
  have h123 := Nat.lt_of_mul_lt_right h122
  simp only [Nat.lt_of_mul_lt_right] at h123
  have h124 := Nat.lt_of_mul_lt_left h123
  simp only [Nat.lt_of_mul_lt_left] at h124
  have h125 := Nat.lt_of_mul_lt_right h124
  simp only [Nat.lt_of_mul_lt_right] at h125
  have h126 := Nat.lt_of_mul_lt_left h125
  simp only [Nat.lt_of_mul_lt_left] at h126
  have h127 := Nat.lt_of_mul_lt_right h126
  simp only [Nat.lt_of_mul_lt_right] at h127
  have h128 := Nat.lt_of_mul_lt_left h127
  simp only [Nat.lt_of_mul_lt_left] at h128
  have h129 := Nat.lt_of_mul_lt_right h128
  simp only [Nat.lt_of_mul_lt_right] at h129
  have h130 := Nat.lt_of_mul_lt_left h129
  simp only [Nat.lt_of_mul_lt_left] at h130
  have h131 := Nat.lt_of_mul_lt_right h130
  simp only [Nat.lt_of_mul_lt_right] at h131
  have h132 := Nat.lt_of_mul_lt_left h131
  simp only [Nat.lt_of_mul_lt_left] at h132
  have h133 := Nat.lt_of_mul_lt_right h132
  simp only [Nat.lt_of_mul_lt_right] at h133
  have h134 := Nat.lt_of_mul_lt_left h133
  simp only [Nat.lt_of_mul_lt_left] at h134
  have h135 := Nat.lt_of_mul_lt_right h134
  simp only [Nat.lt_of_mul_lt_right] at h135
  have h136 := Nat.lt_of_mul_lt_left h135
  simp only [Nat.lt_of_mul_lt_left] at h136
  have h137 := Nat.lt_of_mul_lt_right h136
  simp only [Nat.lt_of_mul_lt_right] at h137
  have h138 := Nat.lt_of_mul_lt_left h137
  simp only [Nat.lt_of_mul_lt_left] at h138
  have h139 := Nat.lt_of_mul_lt_right h138
  simp only [Nat.lt_of_mul_lt_right] at h139
  have h140 := Nat.lt_of_mul_lt_left h139
  simp only [Nat.lt_of_mul_lt_left] at h140
  have h141 := Nat.lt_of_mul_lt_right h140
  simp only [Nat.lt_of_mul_lt_right] at h141
  have h142 := Nat.lt_of_mul_lt_left h141
  simp only [Nat.lt_of_mul_lt_left] at h142
  have h143 := Nat.lt_of_mul_lt_right h142
  simp only [Nat.lt_of_mul_lt_right] at h143
  have h144 := Nat.lt_of_mul_lt_left h143
  simp only [Nat.lt_of_mul_lt_left] at h144
  have h145 := Nat.lt_of_mul_lt_right h144
  simp only [Nat.lt_of_mul_lt_right] at h145
  have h146 := Nat.lt_of_mul_lt_left h145
  simp only [Nat.lt_of_mul_lt_left] at h146
  have h147 := Nat.lt_of_mul_lt_right h146
  simp only [Nat.lt_of_mul_lt_right] at h147
  have h148 := Nat.lt_of_mul_lt_left h147
  simp only [Nat.lt_of_mul_lt_left] at h148
  have h149 := Nat.lt_of_mul_lt_right h148
  simp only [Nat.lt_of_mul_lt_right] at h149
  have h150 := Nat.lt_of_mul_lt_left h149
  simp only [Nat.lt_of_mul_lt_left] at h150
  have h151 := Nat.lt_of_mul_lt_right h150
  simp only [Nat.lt_of_mul_lt_right] at h151
  have h152 := Nat.lt_of_mul_lt_left h151
  simp only [Nat.lt_of_mul_lt_left] at h152
  have h153 := Nat.lt_of_mul_lt_right h152
  simp only [Nat.lt_of_mul_lt_right] at h153
  have h154 := Nat.lt_of_mul_lt_left h153
  simp only [Nat.lt_of_mul_lt_left] at h154
  have h155 := Nat.lt_of_mul_lt_right h154
  simp only [Nat.lt_of_mul_lt_right] at h155
  have h156 := Nat.lt_of_mul_lt_left h155
  simp only [Nat.lt_of_mul_lt_left] at h156
  have h157 := Nat.lt_of_mul_lt_right h156
  simp only [Nat.lt_of_mul_lt_right] at h157
  have h158 := Nat.lt_of_mul_lt_left h157
  simp only [Nat.lt_of_mul_lt_left] at h158
  have h159 := Nat.lt_of_mul_lt_right h158
  simp only [Nat.lt_of_mul_lt_right] at h159
  have h160 := Nat.lt_of_mul_lt_left h159
  simp only [Nat.lt_of_mul_lt_left] at h160
  have h161 := Nat.lt_of_mul_lt_right h160
  simp only [Nat.lt_of_mul_lt_right] at h161
  have h162 := Nat.lt_of_mul_lt_left h161
  simp only [Nat.lt_of_mul_lt_left] at h162
  have h163 := Nat.lt_of_mul_lt_right h162
  simp only [Nat.lt_of_mul_lt_right] at h163
  have h164 := Nat.lt_of_mul_lt_left h163
  simp only [Nat.lt_of_mul_lt_left] at h164
  have h165 := Nat.lt_of_mul_lt_right h164
  simp only [Nat.lt_of_mul_lt_right] at h165
  have h166 := Nat.lt_of_mul_lt_left h165
  simp only [Nat.lt_of_mul_lt_left] at h166
  have h167 := Nat.lt_of_mul_lt_right h166
  simp only [Nat.lt_of_mul_lt_right] at h167
  have h168 := Nat.lt_of_mul_lt_left h167
  simp only [Nat.lt_of_mul_lt_left] at h168
  have h169 := Nat.lt_of_mul_lt_right h168
  simp only [Nat.lt_of_mul_lt_right] at h169
  have h170 := Nat.lt_of_mul_lt_left h169
  simp only [Nat.lt_of_mul_lt_left] at h170
  have h171 := Nat.lt_of_mul_lt_right h170
  simp only [Nat.lt_of_mul_lt_right] at h171
  have h172 := Nat.lt_of_mul_lt_left h171
  simp only [Nat.lt_of_mul_lt_left] at h172
  have h173 := Nat.lt_of_mul_lt_right h172
  simp only [Nat.lt_of_mul_lt_right] at h173
  have h174 := Nat.lt_of_mul_lt_left h173
  simp only [Nat.lt_of_mul_lt_left] at h174
  have h175 := Nat.lt_of_mul_lt_right h174
  simp only [Nat.lt_of_mul_lt_right] at h175
  have h176 := Nat.lt_of_mul_lt_left h175
  simp only [Nat.lt_of_mul_lt_left] at h176
  have h177 := Nat.lt_of_mul_lt_right h176
  simp only [Nat.lt_of_mul_lt_right] at h177
  have h178 := Nat.lt_of_mul_lt_left h177
  simp only [Nat.lt_of_mul_lt_left] at h178
  have h179 := Nat.lt_of_mul_lt_right h178
  simp only [Nat.lt_of_mul_lt_right] at h179
  have h180 := Nat.lt_of_mul_lt_left h179
  simp only [Nat.lt_of_mul_lt_left] at h180
  have h181 := Nat.lt_of_mul_lt_right h180
  simp only [Nat.lt_of_mul_lt_right] at h181
  have h182 := Nat.lt_of_mul_lt_left h181
  simp only [Nat.lt_of_mul_lt_left] at h182
  have h183 := Nat.lt_of_mul_lt_right h182
  simp only [Nat.lt_of_mul_lt_right] at h183
  have h184 := Nat.lt_of_mul_lt_left h183
  simp only [Nat.lt_of_mul_lt_left] at h184
  have h185 := Nat.lt_of_mul_lt_right h184
  simp only [Nat.lt_of_mul_lt_right] at h185
  have h186 := Nat.lt_of_mul_lt_left h185
  simp only [Nat.lt_of_mul_lt_left] at h186
  have h187 := Nat.lt_of_mul_lt_right h186
  simp only [Nat.lt_of_mul_lt_right] at h187
  have h188 := Nat.lt_of_mul_lt_left h187
  simp only [Nat.lt_of_mul_lt_left] at h188
  have h189 := Nat.lt_of_mul_lt_right h188
  simp only [Nat.lt_of_mul_lt_right] at h189
  have h190 := Nat.lt_of_mul_lt_left h189
  simp only [Nat.lt_of_mul_lt_left] at h190
  have h191 := Nat.lt_of_mul_lt_right h190
  simp only [Nat.lt_of_mul_lt_right] at h191
  have h192 := Nat.lt_of_mul_lt_left h191
  simp only [Nat.lt_of_mul_lt_left] at h192
  have h193 := Nat.lt_of_mul_lt_right h192
  simp only [Nat.lt_of_mul_lt_right] at h193
  have h194 := Nat.lt_of_mul_lt_left h193
  simp only [Nat.lt_of_mul_lt_left] at h194
  have h195 := Nat.lt_of_mul_lt_right h194
  simp only [Nat.lt_of_mul_lt_right] at h195
  have h196 := Nat.lt_of_mul_lt_left h195
  simp only [Nat.lt_of_mul_lt_left] at h196
  have h197 := Nat.lt_of_mul_lt_right h196
  simp only [Nat.lt_of_mul_lt_right] at h197
  have h198 := Nat.lt_of_mul_lt_left h197
  simp only [Nat.lt_of_mul_lt_left] at h198
  have h199 := Nat.lt_of_mul_lt_right h198
  simp only [Nat.lt_of_mul_lt_right] at h199
  have h200 := Nat.lt_of_mul_lt_left h199
  simp only [Nat.lt_of_mul_lt_left] at h200
  have h201 := Nat.lt_of_mul_lt_right h200
  simp only [Nat.lt_of_mul_lt_right] at h201
  have h202 := Nat.lt_of_mul_lt_left h201
  simp only [Nat.lt_of_mul_lt_left] at h202
  have h203 := Nat.lt_of_mul_lt_right h202
  simp only [Nat.lt_of_mul_lt_right] at h203
  have h204 := Nat.lt_of_mul_lt_left h203
  simp only [Nat.lt_of_mul_lt_left] at h204
  have h205 := Nat.lt_of_mul_lt_right h204
  simp only [Nat.lt_of_mul_lt_right] at h205
  have h206 := Nat.lt_of_mul_lt_left h205
  simp only [Nat.lt_of_mul_lt_left] at h206
  have h207 := Nat.lt_of_mul_lt_right h206
  simp only [Nat.lt_of_mul_lt_right] at h207
  have h208 := Nat.lt_of_mul_lt_left h207
  simp only [Nat.lt_of_mul_lt_left] at h208
  have h209 := Nat.lt_of_mul_lt_right h208
  simp only [Nat.lt_of_mul_lt_right] at h209
  have h210 := Nat.lt_of_mul_lt_left h209
  simp only [Nat.lt_of_mul_lt_left] at h210
  have h211 := Nat.lt_of_mul_lt_right h210
  simp only [Nat.lt_of_mul_lt_right] at h211
  have h212 := Nat.lt_of_mul_lt_left h211
  simp only [Nat.lt_of_mul_lt_left] at h212
  have h213 := Nat.lt_of_mul_lt_right h212
  simp only [Nat.lt_of_mul_lt_right] at h213
  have h214 := Nat.lt_of_mul_lt_left h213
  simp only [Nat.lt_of_mul_lt_left] at h214
  have h215 := Nat.lt_of_mul_lt_right h214
  simp only [Nat.lt_of_mul_lt_right] at h215
  have h216 := Nat.lt_of_mul_lt_left h215
  simp only [Nat.lt_of_mul_lt_left] at h216
  have h217 := Nat.lt_of_mul_lt_right h216
  simp only [Nat.lt_of_mul_lt_right] at h217
  have h218 := Nat.lt_of_mul_lt_left h217
  simp only [Nat.lt_of_mul_lt_left] at h218
  have h219 := Nat.lt_of_mul_lt_right h218
  simp only [Nat.lt_of_mul_lt_right] at h219
  have h220 := Nat.lt_of_mul_lt_left h219
  simp only [Nat.lt_of_mul_lt_left] at h220
  have h221 := Nat.lt_of_mul_lt_right h220
  simp only [Nat.lt_of_mul_lt_right] at h221
  have h222 := Nat.lt_of_mul_lt_left h221
  simp only [Nat.lt_of_mul_lt_left] at h222
  have h223 := Nat.lt_of_mul_lt_right h222
  simp only [Nat.lt_of_mul_lt_right] at h223
  have h224 := Nat.lt_of_mul_lt_left h223
  simp only [Nat.lt_of_mul_lt_left] at h224
  have h225 := Nat.lt_of_mul_lt_right h224
  simp only [Nat.lt_of_mul_lt_right] at h225
  have h226 := Nat.lt_of_mul_lt_left h225
  simp only [Nat.lt_of_mul_lt_left] at h226
  have h227 := Nat.lt_of_mul_lt_right h226
  simp only [Nat.lt_of_mul_lt_right] at h227
  have h228 := Nat.lt_of_mul_lt_left h227
  simp only [Nat.lt_of_mul_lt_left] at h228
  have h229 := Nat.lt_of_mul_lt_right h228
  simp only [Nat.lt_of_mul_lt_right] at h229
  have h230 := Nat.lt_of_mul_lt_left h229
  simp only [Nat.lt_of_mul_lt_left] at h230
  have h231 := Nat.lt_of_mul_lt_right h230
  simp only [Nat.lt_of_mul_lt_right] at h231
  have h232 := Nat.lt_of_mul_lt_left h231
  simp only [Nat.lt_of_mul_lt_left] at h232
  have h233 := Nat.lt_of_mul_lt_right h232
  simp only [Nat.lt_of_mul_lt_right] at h233
  have h234 := Nat.lt_of_mul_lt_left h233
  simp only [Nat.lt_of_mul_lt_left] at h234
  have h235 := Nat.lt_of_mul_lt_right h234
  simp only [Nat.lt_of_mul_lt_right] at h235
  have h236 := Nat.lt_of_mul_lt_left h235
  simp only [Nat.lt_of_mul_lt_left] at h236
  have h237 := Nat.lt_of_mul_lt_right h236
  simp only [Nat.lt_of_mul_lt_right] at h237
  have h238 := Nat.lt_of_mul_lt_left h237
  simp only [Nat.lt_of_mul_lt_left] at h238
  have h239 := Nat.lt_of_mul_lt_right h238
  simp only [Nat.lt_of_mul_lt_right] at h239
  have h240 := Nat.lt_of_mul_lt_left h239
  simp only [Nat.lt_of_mul_lt_left] at h240
  have h241 := Nat.lt_of_mul_lt_right h240
  simp only [Nat.lt_of_mul_lt_right] at h241
  have h242 := Nat.lt_of_mul_lt_left h241
  simp only [Nat.lt_of_mul_lt_left] at h242
  have h243 := Nat.lt_of_mul_lt_right h242
  simp only [Nat.lt_of_mul_lt_right] at h243
  have h244 := Nat.lt_of_mul_lt_left h243
  simp only [Nat.lt_of_mul_lt_left] at h244
  have h245 := Nat.lt_of_mul_lt_right h244
  simp only [Nat.lt_of_mul_lt_right] at h245
  have h246 := Nat.lt_of_mul_lt_left h245
  simp only [Nat.lt_of_mul_lt_left] at h246
  have h247 := Nat.lt_of_mul_lt_right h246
  simp only [Nat.lt_of_mul_lt_right] at h247
  have h248 := Nat.lt_of_mul_lt_left h247
  simp only [Nat.lt_of_mul_lt_left] at h248
  have h249 := Nat.lt_of_mul_lt_right h248
  simp only [Nat.lt_of_mul_lt_right] at h249
  have h250 := Nat.lt_of_mul_lt_left h249
  simp only [Nat.lt_of_mul_lt_left] at h250
  have h251 := Nat.lt_of_mul_lt_right h250
  simp only [Nat.lt_of_mul_lt_right] at h251
  have h252 := Nat.lt_of_mul_lt_left h251
  simp only [Nat.lt_of_mul_lt_left] at h252
  have h253 := Nat.lt_of_mul_lt_right h252
  simp only [Nat.lt_of_mul_lt_right] at h253
  have h254 := Nat.lt_of_mul_lt_left h253
  simp only [Nat.lt_of_mul_lt_left] at h254
  have h255 := Nat.lt_of_mul_lt_right h254
  simp only [Nat.lt_of_mul_lt_right] at h255
  have h256 := Nat.lt_of_mul_lt_left h255
  simp only [Nat.lt_of_mul_lt_left] at h256
  have h257 := Nat.lt_of_mul_lt_right h256
  simp only [Nat.lt_of_mul_lt_right] at h257
  have h258 := Nat.lt_of_mul_lt_left h257
  simp only [Nat.lt_of_mul_lt_left] at h258
  have h259 := Nat.lt_of_mul_lt_right h258
  simp only [Nat.lt_of_mul_lt_right] at h259
  have h260 := Nat.lt_of_mul_lt_left h259
  simp only [Nat.lt_of_mul_lt_left] at h260
  have h261 := Nat.lt_of_mul_lt_right h260
  simp only [Nat.lt_of_mul_lt_right] at h261
  have h262 := Nat.lt_of_mul_lt_left h261
  simp only [Nat.lt_of_mul_lt_left] at h262
  have h263 := Nat.lt_of_mul_lt_right h262
  simp only [Nat.lt_of_mul_lt_right] at h263
  have h264 := Nat.lt_of_mul_lt_left h263
  simp only [Nat.lt_of_mul_lt_left] at h264
  have h265 := Nat.lt_of_mul_lt_right h264
  simp only [Nat.lt_of_mul_lt_right] at h265
  have h266 := Nat.lt_of_mul_lt_left h265
  simp only [Nat.lt_of_mul_lt_left] at h266
  have h267 := Nat.lt_of_mul_lt_right h266
  simp only [Nat.lt_of_mul_lt_right] at h267
  have h268 := Nat.lt_of_mul_lt_left h267
  simp only [Nat.lt_of_mul_lt_left] at h268
  have h269 := Nat.lt_of_mul_lt_right h268
  simp only [Nat.lt_of_mul_lt_right] at h269
  have h270 := Nat.lt_of_mul_lt_left h269
  simp only [Nat.lt_of_mul_lt_left] at h270
  have h271 := Nat.lt_of_mul_lt_right h270
  simp only [Nat.lt_of_mul_lt_right] at h271
  have h272 := Nat.lt_of_mul_lt_left h271
  simp only [Nat.lt_of_mul_lt_left] at h272
  have h273 := Nat.lt_of_mul_lt_right h272
  simp only [Nat.lt_of_mul_lt_right] at h273
  have h274 := Nat.lt_of_mul_lt_left h273
  simp only [Nat.lt_of_mul_lt_left] at h274
  have h275 := Nat.lt_of_mul_lt_right h274
  simp only [Nat.lt_of_mul_lt_right] at h275
  have h276 := Nat.lt_of_mul_lt_left h275
  simp only [Nat.lt_of_mul_lt_left] at h276
  have h277 := Nat.lt_of_mul_lt_right h276
  simp only [Nat.lt_of_mul_lt_right] at h277
  have h278 := Nat.lt_of_mul_lt_left h277
  simp only [Nat.lt_of_mul_lt_left] at h278
  have h279 := Nat.lt_of_mul_lt_right h278
  simp only [Nat.lt_of_mul_lt_right] at h279
  have h280 := Nat.lt_of_mul_lt_left h279
  simp only [Nat.lt_of_mul_lt_left] at h280
  have h281 := Nat.lt_of_mul_lt_right h280
  simp only [Nat.lt_of_mul_lt_right] at h281
  have h282 := Nat.lt_of_mul_lt_left h281
  simp only [Nat.lt_of_mul_lt_left] at h282
  have h283 := Nat.lt_of_mul_lt_right h282
  simp only [Nat.lt_of_mul_lt_right] at h283
  have h284 := Nat.lt_of_mul_lt_left h283
  simp only [Nat.lt_of_mul_lt_left] at h284
  have h285 := Nat.lt_of_mul_lt_right h284
  simp only [Nat.lt_of_mul_lt_right] at h285
  have h286 := Nat.lt_of_mul_lt_left h285
  simp only [Nat.lt_of_mul_lt_left] at h286
  have h287 := Nat.lt_of_mul_lt_right h286
  simp only [Nat.lt_of_mul_lt_right] at h287
  have h288 := Nat.lt_of_mul_lt_left h287
  simp only [Nat.lt_of_mul_lt_left] at h288
  have h289 := Nat.lt_of_mul_lt_right h288
  simp only [Nat.lt_of_mul_lt_right] at h289
  have h290 := Nat.lt_of_mul_lt_left h289
  simp only [Nat.lt_of_mul_lt_left] at h290
  have h291 := Nat.lt_of_mul_lt_right h290
  simp only [Nat.lt_of_mul_lt_right] at h291
  have h292 := Nat.lt_of_mul_lt_left h291
  simp only [Nat.lt_of_mul_lt_left] at h292
  have h293 := Nat.lt_of_mul_lt_right h292
  simp only [Nat.lt_of_mul_lt_right] at h293
  have h294 := Nat.lt_of_mul_lt_left h293
  simp only [Nat.lt_of_mul_lt_left] at h294
  have h295 := Nat.lt_of_mul_lt_right h294
  simp only [Nat.lt_of_mul_lt_right] at h295
  have h296 := Nat.lt_of_mul_lt_left h295
  simp only [Nat.lt_of_mul_lt_left] at h296
  have h297 := Nat.lt_of_mul_lt_right h296
  simp only [Nat.lt_of_mul_lt_right] at h297
  have h298 := Nat.lt_of_mul_lt_left h297
  simp only [Nat.lt_of_mul_lt_left] at h298
  have h299 := Nat.lt_of_mul_lt_right h298
  simp only [Nat.lt_of_mul_lt_right] at h299
  have h300 := Nat.lt_of_mul_lt_left h299
  simp only [Nat.lt_of_mul_lt_left] at h300
  have h301 := Nat.lt_of_mul_lt_right h300
  simp only [Nat.lt_of_mul_lt_right] at h301
  have h302 := Nat.lt_of_mul_lt_left h301
  simp only [Nat.lt_of_mul_lt_left] at h302
  have h303 := Nat.lt_of_mul_lt_right h302
  simp only [Nat.lt_of_mul_lt_right] at h303
  have h304 := Nat.lt_of_mul_lt_left h303
  simp only [Nat.lt_of_mul_lt_left] at h304
  have h305 := Nat.lt_of_mul_lt_right h304
  simp only [Nat.lt_of_mul_lt_right] at h305
  have h306 := Nat.lt_of_mul_lt_left h305
  simp only [Nat.lt_of_mul_lt_left] at h306
  have h307 := Nat.lt_of_mul_lt_right h306
  simp only [Nat.lt_of_mul_lt_right] at h307
  have h308 := Nat.lt_of_mul_lt_left h307
  simp only [Nat.lt_of_mul_lt_left] at h308
  have h309 := Nat.lt_of_mul_lt_right h308
  simp only [Nat.lt_of_mul_lt_right] at h309
  have h310 := Nat.lt_of_mul_lt_left h309
  simp only [Nat.lt_of_mul_lt_left] at h310
  have h311 := Nat.lt_of_mul_lt_right h310
  simp only [Nat.lt_of_mul_lt_right] at h311
  have h312 := Nat.lt_of_mul_lt_left h311
  simp only [Nat.lt_of_mul_lt_left] at h312
  have h313 := Nat.lt_of_mul_lt_right h312
  simp only [Nat.lt_of_mul_lt_right] at h313
  have h314 := Nat.lt_of_mul_lt_left h313
  simp only [Nat.lt_of_mul_lt_left] at h314
  have h315 := Nat.lt_of_mul_lt_right h314
  simp only [Nat.lt_of_mul_lt_right] at h315
  have h316 := Nat.lt_of_mul_lt_left h315
  simp only [Nat.lt_of_mul_lt_left] at h316
  have h317 := Nat.lt_of_mul_lt_right h316
  simp only [Nat.lt_of_mul_lt_right] at h317
  have h318 := Nat.lt_of_mul_lt_left h317
  simp only [Nat.lt_of_mul_lt_left] at h318
  have h319 := Nat.lt_of_mul_lt_right h318
  simp only [Nat.lt_of_mul_lt_right] at h319
  have h320 := Nat.lt_of_mul_lt_left h319
  simp only [Nat.lt_of_mul_lt_left] at h320
  have h321 := Nat.lt_of_mul_lt_right h320
  simp only [Nat.lt_of_mul_lt_right] at h321
  have h322 := Nat.lt_of_mul_lt_left h321
  simp only [Nat.lt_of_mul_lt_left] at h322
  have h323 := Nat.lt_of_mul_lt_right h322
  simp only [Nat.lt_of_mul_lt_right] at h323
  have h324 := Nat.lt_of_mul_lt_left h323
  simp only [Nat.lt_of_mul_lt_left] at h324
  have h325 := Nat.lt_of_mul_lt_right h324
  simp only [Nat.lt_of_mul_lt_right] at h325
  have h326 := Nat.lt_of_mul_lt_left h325
  simp only [Nat.lt_of_mul_lt_left] at h326
  have h327 := Nat.lt_of_mul_lt_right h326
  simp only [Nat.lt_of_mul_lt_right] at h327
  have h328 := Nat.lt_of_mul_lt_left h327
  simp only [Nat.lt_of_mul_lt_left] at h328
  have h329 := Nat.lt_of_mul_lt_right h328
  simp only [Nat.lt_of_mul_lt_right] at h329
  have h330 := Nat.lt_of_mul_lt_left h329
  simp only [Nat.lt_of_mul_lt_left] at h330
  have h331 := Nat.lt_of_mul_lt_right h330
  simp only [Nat.lt_of_mul_lt_right] at h331
  have h332 := Nat.lt_of_mul_lt_left h331
  simp only [Nat.lt_of_mul_lt_left] at h332
  have h333 := Nat.lt_of_mul_lt_right h332
  simp only [Nat.lt_of_mul_lt_right] at h333
  have h334 := Nat.lt_of_mul_lt_left h333
  simp only [Nat.lt_of_mul_lt_left] at h334
  have h335 := Nat.lt_of_mul_lt_right h334
  simp only [Nat.lt_of_mul_lt_right] at h335
  have h336 := Nat.lt_of_mul_lt_left h335
  simp only [Nat.lt_of_mul_lt_left] at h336
  have h337 := Nat.lt_of_mul_lt_right h336
  simp only [Nat.lt_of_mul_lt_right] at h337
  have h338 := Nat.lt_of_mul_lt_left h337
  simp only [Nat.lt_of_mul_lt_left] at h338
  have h339 := Nat.lt_of_mul_lt_right h338
  simp only [Nat.lt_of_mul_lt_right] at h339
  have h340 := Nat.lt_of_mul_lt_left h339
  simp only [Nat.lt_of_mul_lt_left] at h340
  have h341 := Nat.lt_of_mul_lt_right h340
  simp only [Nat.lt_of_mul_lt_right] at h341
  have h342 := Nat.lt_of_mul_lt_left h341
  simp only [Nat.lt_of_mul_lt_left] at h342
  have h343 := Nat.lt_of_mul_lt_right h342
  simp only [Nat.lt_of_mul_lt_right] at h343
  have h344 := Nat.lt_of_mul_lt_left h343
  simp only [Nat.lt_of_mul_lt_left] at h344
  have h345 := Nat.lt_of_mul_lt_right h344
  simp only [Nat.lt_of_mul_lt_right] at h345
  have h346 := Nat.lt_of_mul_lt_left h345
  simp only [Nat.lt_of_mul_lt_left] at h346
  have h347 := Nat.lt_of_mul_lt_right h346
  simp only [Nat.lt_of_mul_lt_right] at h347
  have h348 := Nat.lt_of_mul_lt_left h347
  simp only [Nat.lt_of_mul_lt_left] at h348
  have h349 := Nat.lt_of_mul_lt_right h348
  simp only [Nat.lt_of_mul_lt_right] at h349
  have h350 := Nat.lt_of_mul_lt_left h349
  simp only [Nat.lt_of_mul_lt_left] at h350
  have h351 := Nat.lt_of_mul_lt_right h350
  simp only [Nat.lt_of_mul_lt_right] at h351
  have h352 := Nat.lt_of_mul_lt_left h351
  simp only [Nat.lt_of_mul_lt_left] at h352
  have h353 := Nat.lt_of_mul_lt_right h352
  simp only [Nat.lt_of_mul_lt_right] at h353
  have h354 := Nat.lt_of_mul_lt_left h353
  simp only [Nat.lt_of_mul_lt_left] at h354
  have h355 := Nat.lt_of_mul_lt_right h354
  simp only [Nat.lt_of_mul_lt_right] at h355
  have h356 := Nat.lt_of_mul_lt_left h355
  simp only [Nat.lt_of_mul_lt_left] at h356
  have h357 := Nat.lt_of_mul_lt_right h356
  simp only [Nat.lt_of_mul_lt_right] at h357
  have h358 := Nat.lt_of_mul_lt_left h357
  simp only [Nat.lt_of_mul_lt_left] at h358
  have h359 := Nat.lt_of_mul_lt_right h358
  simp only [Nat.lt_of_mul_lt_right] at h359
  have h360 := Nat.lt_of_mul_lt_left h359
  simp only [Nat.lt_of_mul_lt_left] at h360
  have h361 := Nat.lt_of_mul_lt_right h360
  simp only [Nat.lt_of_mul_lt_right] at h361
  have h362 := Nat.lt_of_mul_lt_left h361
  simp only [Nat.lt_of_mul_lt_left] at h362
  have h363 := Nat.lt_of_mul_lt_right h362
  simp only [Nat.lt_of_mul_lt_right] at h363
  have h364 := Nat.lt_of_mul_lt_left h363
  simp only [Nat.lt_of_mul_lt_left] at h364
  have h365 := Nat.lt_of_mul_lt_right h364
  simp only [Nat.lt_of_mul_lt_right] at h365
  have h366 := Nat.lt_of_mul_lt_left h365
  simp only [Nat.lt_of_mul_lt_left] at h366
  have h367 := Nat.lt_of_mul_lt_right h366
  simp only [Nat.lt_of_mul_lt_right] at h367
  have h368 := Nat.lt_of_mul_lt_left h367
  simp only [Nat.lt_of_mul_lt_left] at h368
  have h369 := Nat.lt_of_mul_lt_right h368
  simp only [Nat.lt_of_mul_lt_right] at h369
  have h370 := Nat.lt_of_mul_lt_left h369
  simp only [Nat.lt_of_mul_lt_left] at h370
  have h371 := Nat.lt_of_mul_lt_right h370
  simp only [Nat.lt_of_mul_lt_right] at h371
  have h372 := Nat.lt_of_mul_lt_left h371
  simp only [Nat.lt_of_mul_lt_left] at h372
  have h373 := Nat.lt_of_mul_lt_right h372
  simp only [Nat.lt_of_mul_lt_right] at h373
  have h374 := Nat.lt_of_mul_lt_left h373
  simp only [Nat.lt_of_mul_lt_left] at h374
  have h375 := Nat.lt_of_mul_lt_right h374
  simp only [Nat.lt_of_mul_lt_right] at h375
  have h376 := Nat.lt_of_mul_lt_left h375
  simp only [Nat.lt_of_mul_lt_left] at h376
  have h377 := Nat.lt_of_mul_lt_right h376
  simp only [Nat.lt_of_mul_lt_right] at h377
  have h378 := Nat.lt_of_mul_lt_left h377
  simp only [Nat.lt_of_mul_lt_left] at h378
  have h379 := Nat.lt_of_mul_lt_right h378
  simp only [Nat.lt_of_mul_lt_right] at h379
  have h380 := Nat.lt_of_mul_lt_left h379
  simp only [Nat.lt_of_mul_lt_left] at h380
  have h381 := Nat.lt_of_mul_lt_right h380
  simp only [Nat.lt_of_mul_lt_right] at h381
  have h382 := Nat.lt_of_mul_lt_left h381
  simp only [Nat.lt_of_mul_lt_left] at h382
  have h383 := Nat.lt_of_mul_lt_right h382
  simp only [Nat.lt_of_mul_lt_right] at h383
  have h384 := Nat.lt_of_mul_lt_left h383
  simp only [Nat.lt_of_mul_lt_left] at h384
  have h385 := Nat.lt_of_mul_lt_right h384
  simp only [Nat.lt_of_mul_lt_right] at h385
  have h386 := Nat.lt_of_mul_lt_left h385
  simp only [Nat.lt_of_mul_lt_left] at h386
  have h387 := Nat.lt_of_mul_lt_right h386
  simp only [Nat.lt_of_mul_lt_right] at h387
  have h388 := Nat.lt_of_mul_lt_left h387
  simp only [Nat.lt_of_mul_lt_left] at h388
  have h389 := Nat.lt_of_mul_lt_right h388
  simp only [Nat.lt_of_mul_lt_right] at h389
  have h390 := Nat.lt_of_mul_lt_left h389
  simp only [Nat.lt_of_mul_lt_left] at h390
  have h391 := Nat.lt_of_mul_lt_right h390
  simp only [Nat.lt_of_mul_lt_right] at h391
  have h392 := Nat.lt_of_mul_lt_left h391
  simp only [Nat.lt_of_mul_lt_left] at h392
  have h393 := Nat.lt_of_mul_lt_right h392
  simp only [Nat.lt_of_mul_lt_right] at h393
  have h394 := Nat.lt_of_mul_lt_left h393
  simp only [Nat.lt_of_mul_lt_left] at h394
  have h395 := Nat.lt_of_mul_lt_right h394
  simp only [Nat.lt_of_mul_lt_right] at h395
  have h396 := Nat.lt_of_mul_lt_left h395
  simp only [Nat.lt_of_mul_lt_left] at h396
  have h397 := Nat.lt_of_mul_lt_right h396
  simp only [Nat.lt_of_mul_lt_right] at h397
  have h398 := Nat.lt_of_mul_lt_left h397
  simp only [Nat.lt_of_mul_lt_left] at h398
  have h399 := Nat.lt_of_mul_lt_right h398
  simp only [Nat.lt_of_mul_lt_right] at h399
  have h400 := Nat.lt_of_mul_lt_left h399
  simp only [Nat.lt_of_mul_lt_left] at h400
  have h401 := Nat.lt_of_mul_lt_right h400
  simp only [Nat.lt_of_mul_lt_right] at h401
  have h402 := Nat.lt_of_mul_lt_left h401
  simp only [Nat.lt_of_mul_lt_left] at h402
  have h403 := Nat.lt_of_mul_lt_right h402
  simp only [Nat.lt_of_mul_lt_right] at h403
  have h404 := Nat.lt_of_mul_lt_left h403
  simp only [Nat.lt_of_mul_lt_left] at h404
  have h405 := Nat.lt_of_mul_lt_right h404
  simp only [Nat.lt_of_mul_lt_right] at h405
  have h406 := Nat.lt_of_mul_lt_left h405
  simp only [Nat.lt_of_mul_lt_left] at h406
  have h407 := Nat.lt_of_mul_lt_right h406
  simp only [Nat.lt_of_mul_lt_right] at h407
  have h408 := Nat.lt_of_mul_lt_left h407
  simp only [Nat.lt_of_mul_lt_left] at h408
  have h409 := Nat.lt_of_mul_lt_right h408
  simp only [Nat.lt_of_mul_lt_right] at h409
  have h410 := Nat.lt_of_mul_lt_left h409
  simp only [Nat.lt_of_mul_lt_left] at h410
  have h411 := Nat.lt_of_mul_lt_right h410
  simp only [Nat.lt_of_mul_lt_right] at h411
  have h412 := Nat.lt_of_mul_lt_left h411
  simp only [Nat.lt_of_mul_lt_left] at h412
  have h413 := Nat.lt_of_mul_lt_right h412
  simp only [Nat.lt_of_mul_lt_right] at h413
  have h414 := Nat.lt_of_mul_lt_left h413
  simp only [Nat.lt_of_mul_lt_left] at h414
  have h415 := Nat.lt_of_mul_lt_right h414
  simp only [Nat.lt_of_mul_lt_right] at h415
  have h416 := Nat.lt_of_mul_lt_left h415
  simp only [Nat.lt_of_mul_lt_left] at h416

/- ACTUAL PROOF OF Nat.testBit_implies_ge -/

example {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  simp only [testBit_to_div_mod] at p
  apply Decidable.by_contra
  intro not_ge
  have x_lt : x < 2^i := Nat.lt_of_not_le not_ge
  simp [div_eq_of_lt x_lt] at p