/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustRecipes

/-! Kernel-checked reflected Gram decomposition entries 162 through 242. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

def reflectedGram162 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 3, 2, 1] [2, 1, 3, 2]
    reflectedRecipe312

theorem reflectedGram162_check : reflectedEntryCheck reflectedGram162.2 = true := by decide +kernel

def reflectedGram163 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 3, 2, 1] [2, 3, 1, 2]
    (appendRecipe (appendRecipe reflectedRecipe313 reflectedRecipe314) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 2 [1] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 2 [7, 1] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram163_check : reflectedEntryCheck reflectedGram163.2 = true := by decide +kernel

def reflectedGram164 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 3, 2, 1] [3, 1, 2, 3]
    (appendRecipe (appendRecipe reflectedRecipe141 reflectedRecipe316) (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 3 [1] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 3 [6, 1] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram164_check : reflectedEntryCheck reflectedGram164.2 = true := by decide +kernel

def reflectedGram165 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 3, 2, 1] [3, 2, 1, 3]
    reflectedRecipe315

theorem reflectedGram165_check : reflectedEntryCheck reflectedGram165.2 = true := by decide +kernel

def reflectedGram166 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2, 1] [1, 2, 3]
    reflectedRecipe317

theorem reflectedGram166_check : reflectedEntryCheck reflectedGram166.2 = true := by decide +kernel

def reflectedGram167 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2, 1] [1, 3, 2]
    reflectedRecipe310

theorem reflectedGram167_check : reflectedEntryCheck reflectedGram167.2 = true := by decide +kernel

def reflectedGram168 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [1, 3, 2, 1] [2, 1, 3]
    reflectedRecipe318

theorem reflectedGram168_check : reflectedEntryCheck reflectedGram168.2 = true := by decide +kernel

def reflectedGram169 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2, 1] [2, 3, 1]
    reflectedRecipe319

theorem reflectedGram169_check : reflectedEntryCheck reflectedGram169.2 = true := by decide +kernel

def reflectedGram170 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [1, 3, 2, 1] [3, 1, 2]
    reflectedRecipe320

theorem reflectedGram170_check : reflectedEntryCheck reflectedGram170.2 = true := by decide +kernel

def reflectedGram171 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2, 1] [3, 2, 1]
    reflectedRecipe46

theorem reflectedGram171_check : reflectedEntryCheck reflectedGram171.2 = true := by decide +kernel

def reflectedGram172 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [1, 3, 2, 1] [2, 3]
    reflectedRecipe321

theorem reflectedGram172_check : reflectedEntryCheck reflectedGram172.2 = true := by decide +kernel

def reflectedGram173 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [1, 3, 2, 1] [2, 1]
    reflectedRecipe322

theorem reflectedGram173_check : reflectedEntryCheck reflectedGram173.2 = true := by decide +kernel

def reflectedGram174 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [1, 3, 2, 1] [3, 2]
    reflectedRecipe46

theorem reflectedGram174_check : reflectedEntryCheck reflectedGram174.2 = true := by decide +kernel

def reflectedGram175 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [1, 3, 2, 1] [3, 1]
    reflectedRecipe169

theorem reflectedGram175_check : reflectedEntryCheck reflectedGram175.2 = true := by decide +kernel

def reflectedGram176 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 1, 3, 2] [1, 2, 3, 0]
    reflectedRecipe63

theorem reflectedGram176_check : reflectedEntryCheck reflectedGram176.2 = true := by decide +kernel

def reflectedGram177 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 1, 3, 2] [1, 3, 2, 0]
    reflectedRecipe166

theorem reflectedGram177_check : reflectedEntryCheck reflectedGram177.2 = true := by decide +kernel

def reflectedGram178 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [2, 1, 3, 2] [2, 1, 3, 0]
    reflectedRecipe218

theorem reflectedGram178_check : reflectedEntryCheck reflectedGram178.2 = true := by decide +kernel

def reflectedGram179 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 1, 3, 2] [2, 3, 1, 0]
    reflectedRecipe262

theorem reflectedGram179_check : reflectedEntryCheck reflectedGram179.2 = true := by decide +kernel

def reflectedGram180 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [2, 1, 3, 2] [3, 1, 2, 0]
    reflectedRecipe277

theorem reflectedGram180_check : reflectedEntryCheck reflectedGram180.2 = true := by decide +kernel

def reflectedGram181 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 1, 3, 2] [3, 2, 1, 0]
    reflectedRecipe294

theorem reflectedGram181_check : reflectedEntryCheck reflectedGram181.2 = true := by decide +kernel

def reflectedGram182 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 1, 3, 2] [1, 2, 3, 1]
    (appendRecipe (appendRecipe reflectedRecipe56 reflectedRecipe314) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 1 [2] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 1 [7, 2] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram182_check : reflectedEntryCheck reflectedGram182.2 = true := by decide +kernel

def reflectedGram183 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 1, 3, 2] [1, 3, 2, 1]
    reflectedRecipe312

theorem reflectedGram183_check : reflectedEntryCheck reflectedGram183.2 = true := by decide +kernel

def reflectedGram184 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [2, 1, 3, 2] [2, 1, 3, 2]
    reflectedRecipe323

theorem reflectedGram184_check : reflectedEntryCheck reflectedGram184.2 = true := by decide +kernel

def reflectedGram185 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [2, 1, 3, 2] [2, 3, 1, 2]
    (appendRecipe reflectedRecipe324 (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 2 [1] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram185_check : reflectedEntryCheck reflectedGram185.2 = true := by decide +kernel

def reflectedGram186 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [2, 1, 3, 2] [3, 1, 2, 3]
    (appendRecipe (appendRecipe reflectedRecipe325 reflectedRecipe327) (⟨[], [mkD (1) 1 [2, 1, 3, 2] [] 3 [1] (5) 18, mkD (-1) 1 [2, 1, 3, 2] [] 3 [6, 1] (5) 36, mkD (1) 1 [2, 1, 3, 2] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram186_check : reflectedEntryCheck reflectedGram186.2 = true := by decide +kernel

def reflectedGram187 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [2, 1, 3, 2] [3, 2, 1, 3]
    reflectedRecipe326

theorem reflectedGram187_check : reflectedEntryCheck reflectedGram187.2 = true := by decide +kernel

def reflectedGram188 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 1, 3, 2] [1, 2, 3]
    reflectedRecipe328

theorem reflectedGram188_check : reflectedEntryCheck reflectedGram188.2 = true := by decide +kernel

def reflectedGram189 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 1, 3, 2] [1, 3, 2]
    reflectedRecipe164

theorem reflectedGram189_check : reflectedEntryCheck reflectedGram189.2 = true := by decide +kernel

def reflectedGram190 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [2, 1, 3, 2] [2, 1, 3]
    reflectedRecipe323

theorem reflectedGram190_check : reflectedEntryCheck reflectedGram190.2 = true := by decide +kernel

def reflectedGram191 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 1, 3, 2] [2, 3, 1]
    reflectedRecipe329

theorem reflectedGram191_check : reflectedEntryCheck reflectedGram191.2 = true := by decide +kernel

def reflectedGram192 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [2, 1, 3, 2] [3, 1, 2]
    reflectedRecipe331

theorem reflectedGram192_check : reflectedEntryCheck reflectedGram192.2 = true := by decide +kernel

def reflectedGram193 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 1, 3, 2] [3, 2, 1]
    reflectedRecipe332

theorem reflectedGram193_check : reflectedEntryCheck reflectedGram193.2 = true := by decide +kernel

def reflectedGram194 : ℚ × Entry :=
  reflectedGramEntry (20/3 : ℚ) [2, 1, 3, 2] [2, 3]
    reflectedRecipe334

theorem reflectedGram194_check : reflectedEntryCheck reflectedGram194.2 = true := by decide +kernel

def reflectedGram195 : ℚ × Entry :=
  reflectedGramEntry (-3 : ℚ) [2, 1, 3, 2] [2, 1]
    reflectedRecipe335

theorem reflectedGram195_check : reflectedEntryCheck reflectedGram195.2 = true := by decide +kernel

def reflectedGram196 : ℚ × Entry :=
  reflectedGramEntry (-20/3 : ℚ) [2, 1, 3, 2] [3, 2]
    reflectedRecipe336

theorem reflectedGram196_check : reflectedEntryCheck reflectedGram196.2 = true := by decide +kernel

def reflectedGram197 : ℚ × Entry :=
  reflectedGramEntry (3 : ℚ) [2, 1, 3, 2] [3, 1]
    reflectedRecipe338

theorem reflectedGram197_check : reflectedEntryCheck reflectedGram197.2 = true := by decide +kernel

def reflectedGram198 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 3, 1, 2] [1, 2, 3, 0]
    reflectedRecipe83

theorem reflectedGram198_check : reflectedEntryCheck reflectedGram198.2 = true := by decide +kernel

def reflectedGram199 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 3, 1, 2] [1, 3, 2, 0]
    reflectedRecipe168

theorem reflectedGram199_check : reflectedEntryCheck reflectedGram199.2 = true := by decide +kernel

def reflectedGram200 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [2, 3, 1, 2] [2, 1, 3, 0]
    reflectedRecipe224

theorem reflectedGram200_check : reflectedEntryCheck reflectedGram200.2 = true := by decide +kernel

def reflectedGram201 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 3, 1, 2] [2, 3, 1, 0]
    reflectedRecipe167

theorem reflectedGram201_check : reflectedEntryCheck reflectedGram201.2 = true := by decide +kernel

def reflectedGram202 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [2, 3, 1, 2] [3, 1, 2, 0]
    reflectedRecipe223

theorem reflectedGram202_check : reflectedEntryCheck reflectedGram202.2 = true := by decide +kernel

def reflectedGram203 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 3, 1, 2] [3, 2, 1, 0]
    reflectedRecipe76

theorem reflectedGram203_check : reflectedEntryCheck reflectedGram203.2 = true := by decide +kernel

def reflectedGram204 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 3, 1, 2] [1, 2, 3, 1]
    reflectedRecipe299

theorem reflectedGram204_check : reflectedEntryCheck reflectedGram204.2 = true := by decide +kernel

def reflectedGram205 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 3, 1, 2] [1, 3, 2, 1]
    (appendRecipe (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe339) reflectedRecipe300) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 1 [3] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 1 [6, 3] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram205_check : reflectedEntryCheck reflectedGram205.2 = true := by decide +kernel

def reflectedGram206 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [2, 3, 1, 2] [2, 1, 3, 2]
    (appendRecipe reflectedRecipe341 (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 2 [1] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 2 [7, 1] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram206_check : reflectedEntryCheck reflectedGram206.2 = true := by decide +kernel

def reflectedGram207 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [2, 3, 1, 2] [2, 3, 1, 2]
    reflectedRecipe340

theorem reflectedGram207_check : reflectedEntryCheck reflectedGram207.2 = true := by decide +kernel

def reflectedGram208 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [2, 3, 1, 2] [3, 1, 2, 3]
    reflectedRecipe342

theorem reflectedGram208_check : reflectedEntryCheck reflectedGram208.2 = true := by decide +kernel

def reflectedGram209 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [2, 3, 1, 2] [3, 2, 1, 3]
    (appendRecipe (appendRecipe reflectedRecipe70 reflectedRecipe343) (⟨[], [mkD (1) 1 [2, 3, 1, 2] [] 3 [1] (5) 18, mkD (-1) 1 [2, 3, 1, 2] [] 3 [6, 1] (5) 36, mkD (1) 1 [2, 3, 1, 2] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram209_check : reflectedEntryCheck reflectedGram209.2 = true := by decide +kernel

def reflectedGram210 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 3, 1, 2] [1, 2, 3]
    reflectedRecipe344

theorem reflectedGram210_check : reflectedEntryCheck reflectedGram210.2 = true := by decide +kernel

def reflectedGram211 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 3, 1, 2] [1, 3, 2]
    reflectedRecipe345

theorem reflectedGram211_check : reflectedEntryCheck reflectedGram211.2 = true := by decide +kernel

def reflectedGram212 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [2, 3, 1, 2] [2, 1, 3]
    reflectedRecipe346

theorem reflectedGram212_check : reflectedEntryCheck reflectedGram212.2 = true := by decide +kernel

def reflectedGram213 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 3, 1, 2] [2, 3, 1]
    reflectedRecipe340

theorem reflectedGram213_check : reflectedEntryCheck reflectedGram213.2 = true := by decide +kernel

def reflectedGram214 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [2, 3, 1, 2] [3, 1, 2]
    reflectedRecipe222

theorem reflectedGram214_check : reflectedEntryCheck reflectedGram214.2 = true := by decide +kernel

def reflectedGram215 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 3, 1, 2] [3, 2, 1]
    reflectedRecipe347

theorem reflectedGram215_check : reflectedEntryCheck reflectedGram215.2 = true := by decide +kernel

def reflectedGram216 : ℚ × Entry :=
  reflectedGramEntry (-20/3 : ℚ) [2, 3, 1, 2] [2, 3]
    reflectedRecipe333

theorem reflectedGram216_check : reflectedEntryCheck reflectedGram216.2 = true := by decide +kernel

def reflectedGram217 : ℚ × Entry :=
  reflectedGramEntry (3 : ℚ) [2, 3, 1, 2] [2, 1]
    reflectedRecipe348

theorem reflectedGram217_check : reflectedEntryCheck reflectedGram217.2 = true := by decide +kernel

def reflectedGram218 : ℚ × Entry :=
  reflectedGramEntry (20/3 : ℚ) [2, 3, 1, 2] [3, 2]
    reflectedRecipe179

theorem reflectedGram218_check : reflectedEntryCheck reflectedGram218.2 = true := by decide +kernel

def reflectedGram219 : ℚ × Entry :=
  reflectedGramEntry (-3 : ℚ) [2, 3, 1, 2] [3, 1]
    reflectedRecipe337

theorem reflectedGram219_check : reflectedEntryCheck reflectedGram219.2 = true := by decide +kernel

def reflectedGram220 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 1, 2, 3] [1, 2, 3, 0]
    reflectedRecipe86

theorem reflectedGram220_check : reflectedEntryCheck reflectedGram220.2 = true := by decide +kernel

def reflectedGram221 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 1, 2, 3] [1, 3, 2, 0]
    reflectedRecipe176

theorem reflectedGram221_check : reflectedEntryCheck reflectedGram221.2 = true := by decide +kernel

def reflectedGram222 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [3, 1, 2, 3] [2, 1, 3, 0]
    reflectedRecipe233

theorem reflectedGram222_check : reflectedEntryCheck reflectedGram222.2 = true := by decide +kernel

def reflectedGram223 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 1, 2, 3] [2, 3, 1, 0]
    reflectedRecipe263

theorem reflectedGram223_check : reflectedEntryCheck reflectedGram223.2 = true := by decide +kernel

def reflectedGram224 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [3, 1, 2, 3] [3, 1, 2, 0]
    reflectedRecipe226

theorem reflectedGram224_check : reflectedEntryCheck reflectedGram224.2 = true := by decide +kernel

def reflectedGram225 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 1, 2, 3] [3, 2, 1, 0]
    reflectedRecipe295

theorem reflectedGram225_check : reflectedEntryCheck reflectedGram225.2 = true := by decide +kernel

def reflectedGram226 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 1, 2, 3] [1, 2, 3, 1]
    reflectedRecipe301

theorem reflectedGram226_check : reflectedEntryCheck reflectedGram226.2 = true := by decide +kernel

def reflectedGram227 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 1, 2, 3] [1, 3, 2, 1]
    (appendRecipe (appendRecipe reflectedRecipe170 reflectedRecipe303) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 1 [3] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 1 [6, 3] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram227_check : reflectedEntryCheck reflectedGram227.2 = true := by decide +kernel

def reflectedGram228 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [3, 1, 2, 3] [2, 1, 3, 2]
    (appendRecipe (appendRecipe reflectedRecipe349 reflectedRecipe343) (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 2 [1] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 2 [7, 1] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram228_check : reflectedEntryCheck reflectedGram228.2 = true := by decide +kernel

def reflectedGram229 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [3, 1, 2, 3] [2, 3, 1, 2]
    reflectedRecipe342

theorem reflectedGram229_check : reflectedEntryCheck reflectedGram229.2 = true := by decide +kernel

def reflectedGram230 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [3, 1, 2, 3] [3, 1, 2, 3]
    reflectedRecipe350

theorem reflectedGram230_check : reflectedEntryCheck reflectedGram230.2 = true := by decide +kernel

def reflectedGram231 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [3, 1, 2, 3] [3, 2, 1, 3]
    (appendRecipe reflectedRecipe351 (⟨[], [mkD (1) 1 [3, 1, 2, 3] [] 3 [1] (5) 18, mkD (-1) 1 [3, 1, 2, 3] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 1, 2, 3] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram231_check : reflectedEntryCheck reflectedGram231.2 = true := by decide +kernel

def reflectedGram232 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 1, 2, 3] [1, 2, 3]
    reflectedRecipe84

theorem reflectedGram232_check : reflectedEntryCheck reflectedGram232.2 = true := by decide +kernel

def reflectedGram233 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 1, 2, 3] [1, 3, 2]
    reflectedRecipe352

theorem reflectedGram233_check : reflectedEntryCheck reflectedGram233.2 = true := by decide +kernel

def reflectedGram234 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [3, 1, 2, 3] [2, 1, 3]
    reflectedRecipe354

theorem reflectedGram234_check : reflectedEntryCheck reflectedGram234.2 = true := by decide +kernel

def reflectedGram235 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 1, 2, 3] [2, 3, 1]
    reflectedRecipe355

theorem reflectedGram235_check : reflectedEntryCheck reflectedGram235.2 = true := by decide +kernel

def reflectedGram236 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [3, 1, 2, 3] [3, 1, 2]
    reflectedRecipe350

theorem reflectedGram236_check : reflectedEntryCheck reflectedGram236.2 = true := by decide +kernel

def reflectedGram237 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 1, 2, 3] [3, 2, 1]
    reflectedRecipe356

theorem reflectedGram237_check : reflectedEntryCheck reflectedGram237.2 = true := by decide +kernel

def reflectedGram238 : ℚ × Entry :=
  reflectedGramEntry (-20/3 : ℚ) [3, 1, 2, 3] [2, 3]
    reflectedRecipe357

theorem reflectedGram238_check : reflectedEntryCheck reflectedGram238.2 = true := by decide +kernel

def reflectedGram239 : ℚ × Entry :=
  reflectedGramEntry (3 : ℚ) [3, 1, 2, 3] [2, 1]
    reflectedRecipe359

theorem reflectedGram239_check : reflectedEntryCheck reflectedGram239.2 = true := by decide +kernel

def reflectedGram240 : ℚ × Entry :=
  reflectedGramEntry (20/3 : ℚ) [3, 1, 2, 3] [3, 2]
    reflectedRecipe361

theorem reflectedGram240_check : reflectedEntryCheck reflectedGram240.2 = true := by decide +kernel

def reflectedGram241 : ℚ × Entry :=
  reflectedGramEntry (-3 : ℚ) [3, 1, 2, 3] [3, 1]
    reflectedRecipe362

theorem reflectedGram241_check : reflectedEntryCheck reflectedGram241.2 = true := by decide +kernel

def reflectedGram242 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 2, 1, 3] [1, 2, 3, 0]
    reflectedRecipe96

theorem reflectedGram242_check : reflectedEntryCheck reflectedGram242.2 = true := by decide +kernel

def reflectedGramBlock3 : List (ℚ × Entry) :=
  [reflectedGram162,
  reflectedGram163,
  reflectedGram164,
  reflectedGram165,
  reflectedGram166,
  reflectedGram167,
  reflectedGram168,
  reflectedGram169,
  reflectedGram170,
  reflectedGram171,
  reflectedGram172,
  reflectedGram173,
  reflectedGram174,
  reflectedGram175,
  reflectedGram176,
  reflectedGram177,
  reflectedGram178,
  reflectedGram179,
  reflectedGram180,
  reflectedGram181,
  reflectedGram182,
  reflectedGram183,
  reflectedGram184,
  reflectedGram185,
  reflectedGram186,
  reflectedGram187,
  reflectedGram188,
  reflectedGram189,
  reflectedGram190,
  reflectedGram191,
  reflectedGram192,
  reflectedGram193,
  reflectedGram194,
  reflectedGram195,
  reflectedGram196,
  reflectedGram197,
  reflectedGram198,
  reflectedGram199,
  reflectedGram200,
  reflectedGram201,
  reflectedGram202,
  reflectedGram203,
  reflectedGram204,
  reflectedGram205,
  reflectedGram206,
  reflectedGram207,
  reflectedGram208,
  reflectedGram209,
  reflectedGram210,
  reflectedGram211,
  reflectedGram212,
  reflectedGram213,
  reflectedGram214,
  reflectedGram215,
  reflectedGram216,
  reflectedGram217,
  reflectedGram218,
  reflectedGram219,
  reflectedGram220,
  reflectedGram221,
  reflectedGram222,
  reflectedGram223,
  reflectedGram224,
  reflectedGram225,
  reflectedGram226,
  reflectedGram227,
  reflectedGram228,
  reflectedGram229,
  reflectedGram230,
  reflectedGram231,
  reflectedGram232,
  reflectedGram233,
  reflectedGram234,
  reflectedGram235,
  reflectedGram236,
  reflectedGram237,
  reflectedGram238,
  reflectedGram239,
  reflectedGram240,
  reflectedGram241,
  reflectedGram242]

theorem reflectedGramBlock3_check :
    reflectedGramBlock3.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramBlock3, List.all_cons, List.all_nil, Bool.and_true,
    reflectedGram162_check,
    reflectedGram163_check,
    reflectedGram164_check,
    reflectedGram165_check,
    reflectedGram166_check,
    reflectedGram167_check,
    reflectedGram168_check,
    reflectedGram169_check,
    reflectedGram170_check,
    reflectedGram171_check,
    reflectedGram172_check,
    reflectedGram173_check,
    reflectedGram174_check,
    reflectedGram175_check,
    reflectedGram176_check,
    reflectedGram177_check,
    reflectedGram178_check,
    reflectedGram179_check,
    reflectedGram180_check,
    reflectedGram181_check,
    reflectedGram182_check,
    reflectedGram183_check,
    reflectedGram184_check,
    reflectedGram185_check,
    reflectedGram186_check,
    reflectedGram187_check,
    reflectedGram188_check,
    reflectedGram189_check,
    reflectedGram190_check,
    reflectedGram191_check,
    reflectedGram192_check,
    reflectedGram193_check,
    reflectedGram194_check,
    reflectedGram195_check,
    reflectedGram196_check,
    reflectedGram197_check,
    reflectedGram198_check,
    reflectedGram199_check,
    reflectedGram200_check,
    reflectedGram201_check,
    reflectedGram202_check,
    reflectedGram203_check,
    reflectedGram204_check,
    reflectedGram205_check,
    reflectedGram206_check,
    reflectedGram207_check,
    reflectedGram208_check,
    reflectedGram209_check,
    reflectedGram210_check,
    reflectedGram211_check,
    reflectedGram212_check,
    reflectedGram213_check,
    reflectedGram214_check,
    reflectedGram215_check,
    reflectedGram216_check,
    reflectedGram217_check,
    reflectedGram218_check,
    reflectedGram219_check,
    reflectedGram220_check,
    reflectedGram221_check,
    reflectedGram222_check,
    reflectedGram223_check,
    reflectedGram224_check,
    reflectedGram225_check,
    reflectedGram226_check,
    reflectedGram227_check,
    reflectedGram228_check,
    reflectedGram229_check,
    reflectedGram230_check,
    reflectedGram231_check,
    reflectedGram232_check,
    reflectedGram233_check,
    reflectedGram234_check,
    reflectedGram235_check,
    reflectedGram236_check,
    reflectedGram237_check,
    reflectedGram238_check,
    reflectedGram239_check,
    reflectedGram240_check,
    reflectedGram241_check,
    reflectedGram242_check]

end AlbertSequential.FiveTest
