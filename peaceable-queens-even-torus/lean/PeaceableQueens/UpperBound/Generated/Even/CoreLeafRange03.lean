import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange04
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled03Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_150 : ProfileBox := branch_box_150
def node_box_151 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (3 : ℚ) / 160, (39 : ℚ) / 40, (3 : ℚ) / 160], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (7 : ℚ) / 320, (1 : ℚ) / 1, (7 : ℚ) / 320] }
def node_box_152 : ProfileBox := branch_box_152
def node_box_153 : ProfileBox := branch_box_153
def node_box_154 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (19 : ℚ) / 20, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_155 : ProfileBox := branch_box_155
def node_box_156 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_157 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_158 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_159 : ProfileBox := branch_box_159
def node_box_160 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_161 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_162 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_163 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_164 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_165 : ProfileBox := branch_box_165
def node_box_166 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_167 : ProfileBox := branch_box_167
def node_box_168 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_169 : ProfileBox := branch_box_169
def node_box_170 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_171 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 160, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_172 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 160, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_173 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 160, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 32] }
def node_box_174 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 160, (39 : ℚ) / 40, (1 : ℚ) / 32], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_175 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 160, (39 : ℚ) / 40, (1 : ℚ) / 32], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 320, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_176 : ProfileBox := branch_box_176
def node_box_177 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 160, (39 : ℚ) / 40, (1 : ℚ) / 32], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (3 : ℚ) / 320, (1 : ℚ) / 1, (11 : ℚ) / 320] }
def node_box_178 : ProfileBox := branch_box_178
def node_box_179 : ProfileBox := branch_box_179
def node_box_180 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_181 : ProfileBox := branch_box_181
def node_box_182 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_183 : ProfileBox := branch_box_183
def node_box_184 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_185 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_186 : ProfileBox := branch_box_186
def node_box_187 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 160, (1 : ℚ) / 1, (7 : ℚ) / 160] }
def node_box_188 : ProfileBox := branch_box_188
def node_box_189 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 320, (1 : ℚ) / 1, (7 : ℚ) / 160] }
def node_box_190 : ProfileBox := branch_box_190
def node_box_191 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (3 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 320, (1 : ℚ) / 1, (13 : ℚ) / 320] }
def node_box_192 : ProfileBox := branch_box_192
def node_box_193 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_194 : ProfileBox := branch_box_194
def node_box_195 : ProfileBox := branch_box_195
def node_box_196 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_197 : ProfileBox := branch_box_197
def node_box_198 : ProfileBox := { lower := ![(0 : ℚ) / 1, (911 : ℚ) / 1280, (0 : ℚ) / 1, (461 : ℚ) / 640, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (3 : ℚ) / 80] }
def node_box_199 : ProfileBox := branch_box_199

def split_154_accepted : Bool := splitNodeOK node_box_154 node_box_155 node_box_156 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_156_accepted : Bool := splitNodeOK node_box_156 node_box_157 node_box_158 ⟨1, by omega⟩ ((461 : ℚ) / 640)
def split_157_accepted : Bool := splitNodeOK node_box_157 node_box_159 node_box_160 ⟨3, by omega⟩ ((461 : ℚ) / 640)
def split_158_accepted : Bool := splitNodeOK node_box_158 node_box_209 node_box_210 ⟨3, by omega⟩ ((461 : ℚ) / 640)
def split_160_accepted : Bool := splitNodeOK node_box_160 node_box_161 node_box_162 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_161_accepted : Bool := splitNodeOK node_box_161 node_box_163 node_box_164 ⟨7, by omega⟩ ((3 : ℚ) / 80)
def split_162_accepted : Bool := splitNodeOK node_box_162 node_box_193 node_box_194 ⟨7, by omega⟩ ((3 : ℚ) / 80)
def split_163_accepted : Bool := splitNodeOK node_box_163 node_box_165 node_box_166 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_164_accepted : Bool := splitNodeOK node_box_164 node_box_179 node_box_180 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_166_accepted : Bool := splitNodeOK node_box_166 node_box_167 node_box_168 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
def split_168_accepted : Bool := splitNodeOK node_box_168 node_box_169 node_box_170 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
def split_170_accepted : Bool := splitNodeOK node_box_170 node_box_171 node_box_172 ⟨5, by omega⟩ ((1 : ℚ) / 160)
def split_172_accepted : Bool := splitNodeOK node_box_172 node_box_173 node_box_174 ⟨7, by omega⟩ ((1 : ℚ) / 32)
def split_174_accepted : Bool := splitNodeOK node_box_174 node_box_175 node_box_176 ⟨5, by omega⟩ ((3 : ℚ) / 320)
def split_175_accepted : Bool := splitNodeOK node_box_175 node_box_177 node_box_178 ⟨7, by omega⟩ ((11 : ℚ) / 320)
def split_180_accepted : Bool := splitNodeOK node_box_180 node_box_181 node_box_182 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
def split_182_accepted : Bool := splitNodeOK node_box_182 node_box_183 node_box_184 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
def split_184_accepted : Bool := splitNodeOK node_box_184 node_box_185 node_box_186 ⟨5, by omega⟩ ((1 : ℚ) / 160)
def split_185_accepted : Bool := splitNodeOK node_box_185 node_box_187 node_box_188 ⟨7, by omega⟩ ((7 : ℚ) / 160)
def split_187_accepted : Bool := splitNodeOK node_box_187 node_box_189 node_box_190 ⟨5, by omega⟩ ((1 : ℚ) / 320)
def split_189_accepted : Bool := splitNodeOK node_box_189 node_box_191 node_box_192 ⟨7, by omega⟩ ((13 : ℚ) / 320)
def split_193_accepted : Bool := splitNodeOK node_box_193 node_box_195 node_box_196 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_196_accepted : Bool := splitNodeOK node_box_196 node_box_197 node_box_198 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
def split_198_accepted : Bool := splitNodeOK node_box_198 node_box_199 node_box_200 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
def split_batch_03_values : List Bool := [split_154_accepted, split_156_accepted, split_157_accepted, split_158_accepted, split_160_accepted, split_161_accepted, split_162_accepted, split_163_accepted, split_164_accepted, split_166_accepted, split_168_accepted, split_170_accepted, split_172_accepted, split_174_accepted, split_175_accepted, split_180_accepted, split_182_accepted, split_184_accepted, split_185_accepted, split_187_accepted, split_189_accepted, split_193_accepted, split_196_accepted, split_198_accepted]
theorem split_batch_03_ok : split_batch_03_values.all id = true := by
  native_decide

def terminal_151_accepted : Bool := LeafChecks.checkCore node_box_151
def terminal_171_accepted : Bool := LeafChecks.checkCore node_box_171
def terminal_173_accepted : Bool := LeafChecks.checkCore node_box_173
def terminal_177_accepted : Bool := LeafChecks.checkCore node_box_177
def terminal_191_accepted : Bool := LeafChecks.checkCore node_box_191
def terminal_batch_03_values : List Bool := [terminal_151_accepted, terminal_171_accepted, terminal_173_accepted, terminal_177_accepted, terminal_191_accepted]
theorem terminal_batch_03_ok : terminal_batch_03_values.all id = true := by
  native_decide

theorem tree_199 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_199) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_199] using leaf_199_BranchSafe))⟩

theorem split_198_ok : split_198_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_198_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_198 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_198) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_198 node_box_199 node_box_200 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_198_accepted] using split_198_ok) tree_199 tree_200

theorem tree_197 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_197) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_197] using leaf_197_BranchSafe))⟩

theorem split_196_ok : split_196_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_196_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_196 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_196) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_196 node_box_197 node_box_198 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_196_accepted] using split_196_ok) tree_197 tree_198

theorem tree_195 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_195) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_195] using leaf_195_BranchSafe))⟩

theorem tree_194 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_194) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_194] using leaf_194_BranchSafe))⟩

theorem split_193_ok : split_193_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_193_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_193 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_193) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_193 node_box_195 node_box_196 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_193_accepted] using split_193_ok) tree_195 tree_196

theorem tree_192 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_192) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_192] using leaf_192_BranchSafe))⟩

theorem terminal_191_ok : terminal_191_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_03_ok terminal_191_accepted
    (by simp [terminal_batch_03_values])
  exact h
theorem tree_191 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_191) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_191
  simpa [terminal_191_accepted] using terminal_191_ok

theorem tree_190 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_190) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_190] using leaf_190_BranchSafe))⟩

theorem split_189_ok : split_189_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_189_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_189 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_189) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_189 node_box_191 node_box_192 ⟨7, by omega⟩ ((13 : ℚ) / 320)
    (by simpa [split_189_accepted] using split_189_ok) tree_191 tree_192

theorem tree_188 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_188) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_188] using leaf_188_BranchSafe))⟩

theorem split_187_ok : split_187_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_187_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_187 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_187) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_187 node_box_189 node_box_190 ⟨5, by omega⟩ ((1 : ℚ) / 320)
    (by simpa [split_187_accepted] using split_187_ok) tree_189 tree_190

theorem tree_186 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_186) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_186] using leaf_186_BranchSafe))⟩

theorem split_185_ok : split_185_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_185_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_185 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_185) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_185 node_box_187 node_box_188 ⟨7, by omega⟩ ((7 : ℚ) / 160)
    (by simpa [split_185_accepted] using split_185_ok) tree_187 tree_188

theorem split_184_ok : split_184_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_184_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_184 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_184) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_184 node_box_185 node_box_186 ⟨5, by omega⟩ ((1 : ℚ) / 160)
    (by simpa [split_184_accepted] using split_184_ok) tree_185 tree_186

theorem tree_183 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_183) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_183] using leaf_183_BranchSafe))⟩

theorem split_182_ok : split_182_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_182_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_182 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_182) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_182 node_box_183 node_box_184 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_182_accepted] using split_182_ok) tree_183 tree_184

theorem tree_181 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_181) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_181] using leaf_181_BranchSafe))⟩

theorem split_180_ok : split_180_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_180_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_180 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_180) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_180 node_box_181 node_box_182 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_180_accepted] using split_180_ok) tree_181 tree_182

theorem tree_179 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_179) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_179] using leaf_179_BranchSafe))⟩

theorem tree_178 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_178) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_178] using leaf_178_BranchSafe))⟩

theorem terminal_177_ok : terminal_177_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_03_ok terminal_177_accepted
    (by simp [terminal_batch_03_values])
  exact h
theorem tree_177 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_177) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_177
  simpa [terminal_177_accepted] using terminal_177_ok

theorem tree_176 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_176) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_176] using leaf_176_BranchSafe))⟩

theorem split_175_ok : split_175_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_175_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_175 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_175) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_175 node_box_177 node_box_178 ⟨7, by omega⟩ ((11 : ℚ) / 320)
    (by simpa [split_175_accepted] using split_175_ok) tree_177 tree_178

theorem split_174_ok : split_174_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_174_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_174 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_174) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_174 node_box_175 node_box_176 ⟨5, by omega⟩ ((3 : ℚ) / 320)
    (by simpa [split_174_accepted] using split_174_ok) tree_175 tree_176

theorem terminal_173_ok : terminal_173_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_03_ok terminal_173_accepted
    (by simp [terminal_batch_03_values])
  exact h
theorem tree_173 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_173) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_173
  simpa [terminal_173_accepted] using terminal_173_ok

theorem split_172_ok : split_172_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_172_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_172 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_172) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_172 node_box_173 node_box_174 ⟨7, by omega⟩ ((1 : ℚ) / 32)
    (by simpa [split_172_accepted] using split_172_ok) tree_173 tree_174

theorem terminal_171_ok : terminal_171_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_03_ok terminal_171_accepted
    (by simp [terminal_batch_03_values])
  exact h
theorem tree_171 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_171) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_171
  simpa [terminal_171_accepted] using terminal_171_ok

theorem split_170_ok : split_170_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_170_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_170 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_170) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_170 node_box_171 node_box_172 ⟨5, by omega⟩ ((1 : ℚ) / 160)
    (by simpa [split_170_accepted] using split_170_ok) tree_171 tree_172

theorem tree_169 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_169) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_169] using leaf_169_BranchSafe))⟩

theorem split_168_ok : split_168_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_168_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_168 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_168) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_168 node_box_169 node_box_170 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_168_accepted] using split_168_ok) tree_169 tree_170

theorem tree_167 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_167) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_167] using leaf_167_BranchSafe))⟩

theorem split_166_ok : split_166_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_166_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_166 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_166) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_166 node_box_167 node_box_168 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_166_accepted] using split_166_ok) tree_167 tree_168

theorem tree_165 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_165) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_165] using leaf_165_BranchSafe))⟩

theorem split_164_ok : split_164_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_164_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_164 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_164) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_164 node_box_179 node_box_180 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_164_accepted] using split_164_ok) tree_179 tree_180

theorem split_163_ok : split_163_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_163_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_163 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_163) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_163 node_box_165 node_box_166 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_163_accepted] using split_163_ok) tree_165 tree_166

theorem split_162_ok : split_162_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_162_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_162 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_162) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_162 node_box_193 node_box_194 ⟨7, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_162_accepted] using split_162_ok) tree_193 tree_194

theorem split_161_ok : split_161_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_161_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_161 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_161) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_161 node_box_163 node_box_164 ⟨7, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_161_accepted] using split_161_ok) tree_163 tree_164

theorem split_160_ok : split_160_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_160_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_160 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_160) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_160 node_box_161 node_box_162 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_160_accepted] using split_160_ok) tree_161 tree_162

theorem tree_159 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_159) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_159] using leaf_159_BranchSafe))⟩

theorem split_158_ok : split_158_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_158_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_158 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_158) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_158 node_box_209 node_box_210 ⟨3, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_158_accepted] using split_158_ok) tree_209 tree_210

theorem split_157_ok : split_157_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_157_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_157 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_157) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_157 node_box_159 node_box_160 ⟨3, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_157_accepted] using split_157_ok) tree_159 tree_160

theorem split_156_ok : split_156_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_156_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_156 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_156) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_156 node_box_157 node_box_158 ⟨1, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_156_accepted] using split_156_ok) tree_157 tree_158

theorem tree_155 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_155) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_155] using leaf_155_BranchSafe))⟩

theorem split_154_ok : split_154_accepted = true := by
  have h := List.all_eq_true.mp split_batch_03_ok split_154_accepted
    (by simp [split_batch_03_values])
  exact h
theorem tree_154 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_154) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_154 node_box_155 node_box_156 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_154_accepted] using split_154_ok) tree_155 tree_156

theorem tree_153 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_153) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_153] using leaf_153_BranchSafe))⟩

theorem tree_152 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_152) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_152] using leaf_152_BranchSafe))⟩

theorem terminal_151_ok : terminal_151_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_03_ok terminal_151_accepted
    (by simp [terminal_batch_03_values])
  exact h
theorem tree_151 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_151) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_151
  simpa [terminal_151_accepted] using terminal_151_ok

theorem tree_150 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_150) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_150] using leaf_150_BranchSafe))⟩

#print axioms tree_150
end PeaceableQueens.UpperBound.Generated.Even.Core
