/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustRecipes

/-! Kernel-checked reflected Gram decomposition entries 243 through 323. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

def reflectedGram243 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 2, 1, 3] [1, 3, 2, 0]
    reflectedRecipe184

theorem reflectedGram243_check : reflectedEntryCheck reflectedGram243.2 = true := by decide +kernel

def reflectedGram244 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [3, 2, 1, 3] [2, 1, 3, 0]
    reflectedRecipe237

theorem reflectedGram244_check : reflectedEntryCheck reflectedGram244.2 = true := by decide +kernel

def reflectedGram245 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 2, 1, 3] [2, 3, 1, 0]
    reflectedRecipe183

theorem reflectedGram245_check : reflectedEntryCheck reflectedGram245.2 = true := by decide +kernel

def reflectedGram246 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [3, 2, 1, 3] [3, 1, 2, 0]
    reflectedRecipe278

theorem reflectedGram246_check : reflectedEntryCheck reflectedGram246.2 = true := by decide +kernel

def reflectedGram247 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 2, 1, 3] [3, 2, 1, 0]
    reflectedRecipe89

theorem reflectedGram247_check : reflectedEntryCheck reflectedGram247.2 = true := by decide +kernel

def reflectedGram248 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 2, 1, 3] [1, 2, 3, 1]
    (appendRecipe (appendRecipe (scaleRecipe (5/18 : ℚ) reflectedRecipe363) reflectedRecipe316) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 1 [2] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 1 [7, 2] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram248_check : reflectedEntryCheck reflectedGram248.2 = true := by decide +kernel

def reflectedGram249 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 2, 1, 3] [1, 3, 2, 1]
    reflectedRecipe315

theorem reflectedGram249_check : reflectedEntryCheck reflectedGram249.2 = true := by decide +kernel

def reflectedGram250 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [3, 2, 1, 3] [2, 1, 3, 2]
    reflectedRecipe326

theorem reflectedGram250_check : reflectedEntryCheck reflectedGram250.2 = true := by decide +kernel

def reflectedGram251 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [3, 2, 1, 3] [2, 3, 1, 2]
    (appendRecipe (appendRecipe reflectedRecipe180 reflectedRecipe327) (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 2 [1] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 2 [7, 1] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram251_check : reflectedEntryCheck reflectedGram251.2 = true := by decide +kernel

def reflectedGram252 : ℚ × Entry :=
  reflectedGramEntry (-36 : ℚ) [3, 2, 1, 3] [3, 1, 2, 3]
    (appendRecipe reflectedRecipe365 (⟨[], [mkD (1) 1 [3, 2, 1, 3] [] 3 [1] (5) 18, mkD (-1) 1 [3, 2, 1, 3] [] 3 [6, 1] (5) 36, mkD (1) 1 [3, 2, 1, 3] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram252_check : reflectedEntryCheck reflectedGram252.2 = true := by decide +kernel

def reflectedGram253 : ℚ × Entry :=
  reflectedGramEntry (36 : ℚ) [3, 2, 1, 3] [3, 2, 1, 3]
    reflectedRecipe364

theorem reflectedGram253_check : reflectedEntryCheck reflectedGram253.2 = true := by decide +kernel

def reflectedGram254 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 2, 1, 3] [1, 2, 3]
    reflectedRecipe366

theorem reflectedGram254_check : reflectedEntryCheck reflectedGram254.2 = true := by decide +kernel

def reflectedGram255 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 2, 1, 3] [1, 3, 2]
    reflectedRecipe367

theorem reflectedGram255_check : reflectedEntryCheck reflectedGram255.2 = true := by decide +kernel

def reflectedGram256 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [3, 2, 1, 3] [2, 1, 3]
    reflectedRecipe236

theorem reflectedGram256_check : reflectedEntryCheck reflectedGram256.2 = true := by decide +kernel

def reflectedGram257 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 2, 1, 3] [2, 3, 1]
    reflectedRecipe368

theorem reflectedGram257_check : reflectedEntryCheck reflectedGram257.2 = true := by decide +kernel

def reflectedGram258 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [3, 2, 1, 3] [3, 1, 2]
    reflectedRecipe369

theorem reflectedGram258_check : reflectedEntryCheck reflectedGram258.2 = true := by decide +kernel

def reflectedGram259 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 2, 1, 3] [3, 2, 1]
    reflectedRecipe364

theorem reflectedGram259_check : reflectedEntryCheck reflectedGram259.2 = true := by decide +kernel

def reflectedGram260 : ℚ × Entry :=
  reflectedGramEntry (20/3 : ℚ) [3, 2, 1, 3] [2, 3]
    reflectedRecipe69

theorem reflectedGram260_check : reflectedEntryCheck reflectedGram260.2 = true := by decide +kernel

def reflectedGram261 : ℚ × Entry :=
  reflectedGramEntry (-3 : ℚ) [3, 2, 1, 3] [2, 1]
    reflectedRecipe358

theorem reflectedGram261_check : reflectedEntryCheck reflectedGram261.2 = true := by decide +kernel

def reflectedGram262 : ℚ × Entry :=
  reflectedGramEntry (-20/3 : ℚ) [3, 2, 1, 3] [3, 2]
    reflectedRecipe360

theorem reflectedGram262_check : reflectedEntryCheck reflectedGram262.2 = true := by decide +kernel

def reflectedGram263 : ℚ × Entry :=
  reflectedGramEntry (3 : ℚ) [3, 2, 1, 3] [3, 1]
    reflectedRecipe370

theorem reflectedGram263_check : reflectedEntryCheck reflectedGram263.2 = true := by decide +kernel

def reflectedGram264 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3] [1, 2, 3, 0]
    reflectedRecipe0

theorem reflectedGram264_check : reflectedEntryCheck reflectedGram264.2 = true := by decide +kernel

def reflectedGram265 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3] [1, 3, 2, 0]
    reflectedRecipe135

theorem reflectedGram265_check : reflectedEntryCheck reflectedGram265.2 = true := by decide +kernel

def reflectedGram266 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 2, 3] [2, 1, 3, 0]
    reflectedRecipe201

theorem reflectedGram266_check : reflectedEntryCheck reflectedGram266.2 = true := by decide +kernel

def reflectedGram267 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3] [2, 3, 1, 0]
    reflectedRecipe250

theorem reflectedGram267_check : reflectedEntryCheck reflectedGram267.2 = true := by decide +kernel

def reflectedGram268 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 2, 3] [3, 1, 2, 0]
    reflectedRecipe271

theorem reflectedGram268_check : reflectedEntryCheck reflectedGram268.2 = true := by decide +kernel

def reflectedGram269 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3] [3, 2, 1, 0]
    reflectedRecipe288

theorem reflectedGram269_check : reflectedEntryCheck reflectedGram269.2 = true := by decide +kernel

def reflectedGram270 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3] [1, 2, 3, 1]
    reflectedRecipe297

theorem reflectedGram270_check : reflectedEntryCheck reflectedGram270.2 = true := by decide +kernel

def reflectedGram271 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3] [1, 3, 2, 1]
    reflectedRecipe317

theorem reflectedGram271_check : reflectedEntryCheck reflectedGram271.2 = true := by decide +kernel

def reflectedGram272 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 2, 3] [2, 1, 3, 2]
    reflectedRecipe328

theorem reflectedGram272_check : reflectedEntryCheck reflectedGram272.2 = true := by decide +kernel

def reflectedGram273 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 2, 3] [2, 3, 1, 2]
    reflectedRecipe344

theorem reflectedGram273_check : reflectedEntryCheck reflectedGram273.2 = true := by decide +kernel

def reflectedGram274 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 2, 3] [3, 1, 2, 3]
    reflectedRecipe84

theorem reflectedGram274_check : reflectedEntryCheck reflectedGram274.2 = true := by decide +kernel

def reflectedGram275 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 2, 3] [3, 2, 1, 3]
    reflectedRecipe366

theorem reflectedGram275_check : reflectedEntryCheck reflectedGram275.2 = true := by decide +kernel

def reflectedGram276 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3] [1, 2, 3]
    (⟨[mkY (1) 1 [1, 2, 3]], []⟩ : ReflectedRecipe)

theorem reflectedGram276_check : reflectedEntryCheck reflectedGram276.2 = true := by decide +kernel

def reflectedGram277 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3] [1, 3, 2]
    (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe3) (⟨[], [mkD (1) 1 [1, 2] [1] 3 [2] (1) 2]⟩ : ReflectedRecipe))

theorem reflectedGram277_check : reflectedEntryCheck reflectedGram277.2 = true := by decide +kernel

def reflectedGram278 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [1, 2, 3] [2, 1, 3]
    reflectedRecipe25

theorem reflectedGram278_check : reflectedEntryCheck reflectedGram278.2 = true := by decide +kernel

def reflectedGram279 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3] [2, 3, 1]
    reflectedRecipe154

theorem reflectedGram279_check : reflectedEntryCheck reflectedGram279.2 = true := by decide +kernel

def reflectedGram280 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [1, 2, 3] [3, 1, 2]
    reflectedRecipe84

theorem reflectedGram280_check : reflectedEntryCheck reflectedGram280.2 = true := by decide +kernel

def reflectedGram281 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3] [3, 2, 1]
    reflectedRecipe307

theorem reflectedGram281_check : reflectedEntryCheck reflectedGram281.2 = true := by decide +kernel

def reflectedGram282 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [1, 2, 3] [2, 3]
    reflectedRecipe98

theorem reflectedGram282_check : reflectedEntryCheck reflectedGram282.2 = true := by decide +kernel

def reflectedGram283 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [1, 2, 3] [2, 1]
    reflectedRecipe55

theorem reflectedGram283_check : reflectedEntryCheck reflectedGram283.2 = true := by decide +kernel

def reflectedGram284 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [1, 2, 3] [3, 2]
    reflectedRecipe371

theorem reflectedGram284_check : reflectedEntryCheck reflectedGram284.2 = true := by decide +kernel

def reflectedGram285 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [1, 2, 3] [3, 1]
    reflectedRecipe139

theorem reflectedGram285_check : reflectedEntryCheck reflectedGram285.2 = true := by decide +kernel

def reflectedGram286 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2] [1, 2, 3, 0]
    reflectedRecipe21

theorem reflectedGram286_check : reflectedEntryCheck reflectedGram286.2 = true := by decide +kernel

def reflectedGram287 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2] [1, 3, 2, 0]
    reflectedRecipe136

theorem reflectedGram287_check : reflectedEntryCheck reflectedGram287.2 = true := by decide +kernel

def reflectedGram288 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 3, 2] [2, 1, 3, 0]
    reflectedRecipe210

theorem reflectedGram288_check : reflectedEntryCheck reflectedGram288.2 = true := by decide +kernel

def reflectedGram289 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2] [2, 3, 1, 0]
    reflectedRecipe252

theorem reflectedGram289_check : reflectedEntryCheck reflectedGram289.2 = true := by decide +kernel

def reflectedGram290 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 3, 2] [3, 1, 2, 0]
    reflectedRecipe272

theorem reflectedGram290_check : reflectedEntryCheck reflectedGram290.2 = true := by decide +kernel

def reflectedGram291 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2] [3, 2, 1, 0]
    reflectedRecipe290

theorem reflectedGram291_check : reflectedEntryCheck reflectedGram291.2 = true := by decide +kernel

def reflectedGram292 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2] [1, 2, 3, 1]
    reflectedRecipe304

theorem reflectedGram292_check : reflectedEntryCheck reflectedGram292.2 = true := by decide +kernel

def reflectedGram293 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2] [1, 3, 2, 1]
    reflectedRecipe310

theorem reflectedGram293_check : reflectedEntryCheck reflectedGram293.2 = true := by decide +kernel

def reflectedGram294 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 3, 2] [2, 1, 3, 2]
    reflectedRecipe164

theorem reflectedGram294_check : reflectedEntryCheck reflectedGram294.2 = true := by decide +kernel

def reflectedGram295 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 3, 2] [2, 3, 1, 2]
    reflectedRecipe345

theorem reflectedGram295_check : reflectedEntryCheck reflectedGram295.2 = true := by decide +kernel

def reflectedGram296 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 3, 2] [3, 1, 2, 3]
    reflectedRecipe352

theorem reflectedGram296_check : reflectedEntryCheck reflectedGram296.2 = true := by decide +kernel

def reflectedGram297 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 3, 2] [3, 2, 1, 3]
    reflectedRecipe367

theorem reflectedGram297_check : reflectedEntryCheck reflectedGram297.2 = true := by decide +kernel

def reflectedGram298 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2] [1, 2, 3]
    (appendRecipe (scaleRecipe (1/2 : ℚ) reflectedRecipe41) (⟨[], [mkD (1) 1 [1, 3] [1] 2 [3] (1) 2]⟩ : ReflectedRecipe))

theorem reflectedGram298_check : reflectedEntryCheck reflectedGram298.2 = true := by decide +kernel

def reflectedGram299 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2] [1, 3, 2]
    (⟨[mkY (1) 1 [1, 3, 2]], []⟩ : ReflectedRecipe)

theorem reflectedGram299_check : reflectedEntryCheck reflectedGram299.2 = true := by decide +kernel

def reflectedGram300 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [1, 3, 2] [2, 1, 3]
    reflectedRecipe164

theorem reflectedGram300_check : reflectedEntryCheck reflectedGram300.2 = true := by decide +kernel

def reflectedGram301 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2] [2, 3, 1]
    reflectedRecipe319

theorem reflectedGram301_check : reflectedEntryCheck reflectedGram301.2 = true := by decide +kernel

def reflectedGram302 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [1, 3, 2] [3, 1, 2]
    reflectedRecipe140

theorem reflectedGram302_check : reflectedEntryCheck reflectedGram302.2 = true := by decide +kernel

def reflectedGram303 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2] [3, 2, 1]
    reflectedRecipe46

theorem reflectedGram303_check : reflectedEntryCheck reflectedGram303.2 = true := by decide +kernel

def reflectedGram304 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [1, 3, 2] [2, 3]
    reflectedRecipe372

theorem reflectedGram304_check : reflectedEntryCheck reflectedGram304.2 = true := by decide +kernel

def reflectedGram305 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [1, 3, 2] [2, 1]
    reflectedRecipe24

theorem reflectedGram305_check : reflectedEntryCheck reflectedGram305.2 = true := by decide +kernel

def reflectedGram306 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [1, 3, 2] [3, 2]
    reflectedRecipe44

theorem reflectedGram306_check : reflectedEntryCheck reflectedGram306.2 = true := by decide +kernel

def reflectedGram307 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [1, 3, 2] [3, 1]
    reflectedRecipe169

theorem reflectedGram307_check : reflectedEntryCheck reflectedGram307.2 = true := by decide +kernel

def reflectedGram308 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [2, 1, 3] [1, 2, 3, 0]
    reflectedRecipe27

theorem reflectedGram308_check : reflectedEntryCheck reflectedGram308.2 = true := by decide +kernel

def reflectedGram309 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [2, 1, 3] [1, 3, 2, 0]
    reflectedRecipe149

theorem reflectedGram309_check : reflectedEntryCheck reflectedGram309.2 = true := by decide +kernel

def reflectedGram310 : ℚ × Entry :=
  reflectedGramEntry (-21 : ℚ) [2, 1, 3] [2, 1, 3, 0]
    reflectedRecipe211

theorem reflectedGram310_check : reflectedEntryCheck reflectedGram310.2 = true := by decide +kernel

def reflectedGram311 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [2, 1, 3] [2, 3, 1, 0]
    reflectedRecipe253

theorem reflectedGram311_check : reflectedEntryCheck reflectedGram311.2 = true := by decide +kernel

def reflectedGram312 : ℚ × Entry :=
  reflectedGramEntry (21 : ℚ) [2, 1, 3] [3, 1, 2, 0]
    reflectedRecipe274

theorem reflectedGram312_check : reflectedEntryCheck reflectedGram312.2 = true := by decide +kernel

def reflectedGram313 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [2, 1, 3] [3, 2, 1, 0]
    reflectedRecipe292

theorem reflectedGram313_check : reflectedEntryCheck reflectedGram313.2 = true := by decide +kernel

def reflectedGram314 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [2, 1, 3] [1, 2, 3, 1]
    reflectedRecipe305

theorem reflectedGram314_check : reflectedEntryCheck reflectedGram314.2 = true := by decide +kernel

def reflectedGram315 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [2, 1, 3] [1, 3, 2, 1]
    reflectedRecipe318

theorem reflectedGram315_check : reflectedEntryCheck reflectedGram315.2 = true := by decide +kernel

def reflectedGram316 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [2, 1, 3] [2, 1, 3, 2]
    reflectedRecipe323

theorem reflectedGram316_check : reflectedEntryCheck reflectedGram316.2 = true := by decide +kernel

def reflectedGram317 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [2, 1, 3] [2, 3, 1, 2]
    reflectedRecipe346

theorem reflectedGram317_check : reflectedEntryCheck reflectedGram317.2 = true := by decide +kernel

def reflectedGram318 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [2, 1, 3] [3, 1, 2, 3]
    reflectedRecipe354

theorem reflectedGram318_check : reflectedEntryCheck reflectedGram318.2 = true := by decide +kernel

def reflectedGram319 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [2, 1, 3] [3, 2, 1, 3]
    reflectedRecipe236

theorem reflectedGram319_check : reflectedEntryCheck reflectedGram319.2 = true := by decide +kernel

def reflectedGram320 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [2, 1, 3] [1, 2, 3]
    reflectedRecipe55

theorem reflectedGram320_check : reflectedEntryCheck reflectedGram320.2 = true := by decide +kernel

def reflectedGram321 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [2, 1, 3] [1, 3, 2]
    reflectedRecipe164

theorem reflectedGram321_check : reflectedEntryCheck reflectedGram321.2 = true := by decide +kernel

def reflectedGram322 : ℚ × Entry :=
  reflectedGramEntry (49 : ℚ) [2, 1, 3] [2, 1, 3]
    reflectedRecipe373

theorem reflectedGram322_check : reflectedEntryCheck reflectedGram322.2 = true := by decide +kernel

def reflectedGram323 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [2, 1, 3] [2, 3, 1]
    (appendRecipe reflectedRecipe203 (⟨[], [mkD (1) 1 [2, 1] [2] 3 [1] (5) 18]⟩ : ReflectedRecipe))

theorem reflectedGram323_check : reflectedEntryCheck reflectedGram323.2 = true := by decide +kernel

def reflectedGramBlock4 : List (ℚ × Entry) :=
  [reflectedGram243,
  reflectedGram244,
  reflectedGram245,
  reflectedGram246,
  reflectedGram247,
  reflectedGram248,
  reflectedGram249,
  reflectedGram250,
  reflectedGram251,
  reflectedGram252,
  reflectedGram253,
  reflectedGram254,
  reflectedGram255,
  reflectedGram256,
  reflectedGram257,
  reflectedGram258,
  reflectedGram259,
  reflectedGram260,
  reflectedGram261,
  reflectedGram262,
  reflectedGram263,
  reflectedGram264,
  reflectedGram265,
  reflectedGram266,
  reflectedGram267,
  reflectedGram268,
  reflectedGram269,
  reflectedGram270,
  reflectedGram271,
  reflectedGram272,
  reflectedGram273,
  reflectedGram274,
  reflectedGram275,
  reflectedGram276,
  reflectedGram277,
  reflectedGram278,
  reflectedGram279,
  reflectedGram280,
  reflectedGram281,
  reflectedGram282,
  reflectedGram283,
  reflectedGram284,
  reflectedGram285,
  reflectedGram286,
  reflectedGram287,
  reflectedGram288,
  reflectedGram289,
  reflectedGram290,
  reflectedGram291,
  reflectedGram292,
  reflectedGram293,
  reflectedGram294,
  reflectedGram295,
  reflectedGram296,
  reflectedGram297,
  reflectedGram298,
  reflectedGram299,
  reflectedGram300,
  reflectedGram301,
  reflectedGram302,
  reflectedGram303,
  reflectedGram304,
  reflectedGram305,
  reflectedGram306,
  reflectedGram307,
  reflectedGram308,
  reflectedGram309,
  reflectedGram310,
  reflectedGram311,
  reflectedGram312,
  reflectedGram313,
  reflectedGram314,
  reflectedGram315,
  reflectedGram316,
  reflectedGram317,
  reflectedGram318,
  reflectedGram319,
  reflectedGram320,
  reflectedGram321,
  reflectedGram322,
  reflectedGram323]

theorem reflectedGramBlock4_check :
    reflectedGramBlock4.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramBlock4, List.all_cons, List.all_nil, Bool.and_true,
    reflectedGram243_check,
    reflectedGram244_check,
    reflectedGram245_check,
    reflectedGram246_check,
    reflectedGram247_check,
    reflectedGram248_check,
    reflectedGram249_check,
    reflectedGram250_check,
    reflectedGram251_check,
    reflectedGram252_check,
    reflectedGram253_check,
    reflectedGram254_check,
    reflectedGram255_check,
    reflectedGram256_check,
    reflectedGram257_check,
    reflectedGram258_check,
    reflectedGram259_check,
    reflectedGram260_check,
    reflectedGram261_check,
    reflectedGram262_check,
    reflectedGram263_check,
    reflectedGram264_check,
    reflectedGram265_check,
    reflectedGram266_check,
    reflectedGram267_check,
    reflectedGram268_check,
    reflectedGram269_check,
    reflectedGram270_check,
    reflectedGram271_check,
    reflectedGram272_check,
    reflectedGram273_check,
    reflectedGram274_check,
    reflectedGram275_check,
    reflectedGram276_check,
    reflectedGram277_check,
    reflectedGram278_check,
    reflectedGram279_check,
    reflectedGram280_check,
    reflectedGram281_check,
    reflectedGram282_check,
    reflectedGram283_check,
    reflectedGram284_check,
    reflectedGram285_check,
    reflectedGram286_check,
    reflectedGram287_check,
    reflectedGram288_check,
    reflectedGram289_check,
    reflectedGram290_check,
    reflectedGram291_check,
    reflectedGram292_check,
    reflectedGram293_check,
    reflectedGram294_check,
    reflectedGram295_check,
    reflectedGram296_check,
    reflectedGram297_check,
    reflectedGram298_check,
    reflectedGram299_check,
    reflectedGram300_check,
    reflectedGram301_check,
    reflectedGram302_check,
    reflectedGram303_check,
    reflectedGram304_check,
    reflectedGram305_check,
    reflectedGram306_check,
    reflectedGram307_check,
    reflectedGram308_check,
    reflectedGram309_check,
    reflectedGram310_check,
    reflectedGram311_check,
    reflectedGram312_check,
    reflectedGram313_check,
    reflectedGram314_check,
    reflectedGram315_check,
    reflectedGram316_check,
    reflectedGram317_check,
    reflectedGram318_check,
    reflectedGram319_check,
    reflectedGram320_check,
    reflectedGram321_check,
    reflectedGram322_check,
    reflectedGram323_check]

end AlbertSequential.FiveTest
