/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustRecipes

/-! Kernel-checked reflected Gram decomposition entries 324 through 404. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

def reflectedGram324 : ℚ × Entry :=
  reflectedGramEntry (-49 : ℚ) [2, 1, 3] [3, 1, 2]
    reflectedRecipe331

theorem reflectedGram324_check : reflectedEntryCheck reflectedGram324.2 = true := by decide +kernel

def reflectedGram325 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [2, 1, 3] [3, 2, 1]
    reflectedRecipe236

theorem reflectedGram325_check : reflectedEntryCheck reflectedGram325.2 = true := by decide +kernel

def reflectedGram326 : ℚ × Entry :=
  reflectedGramEntry (-70/9 : ℚ) [2, 1, 3] [2, 3]
    reflectedRecipe64

theorem reflectedGram326_check : reflectedEntryCheck reflectedGram326.2 = true := by decide +kernel

def reflectedGram327 : ℚ × Entry :=
  reflectedGramEntry (7/2 : ℚ) [2, 1, 3] [2, 1]
    reflectedRecipe373

theorem reflectedGram327_check : reflectedEntryCheck reflectedGram327.2 = true := by decide +kernel

def reflectedGram328 : ℚ × Entry :=
  reflectedGramEntry (70/9 : ℚ) [2, 1, 3] [3, 2]
    reflectedRecipe68

theorem reflectedGram328_check : reflectedEntryCheck reflectedGram328.2 = true := by decide +kernel

def reflectedGram329 : ℚ × Entry :=
  reflectedGramEntry (-7/2 : ℚ) [2, 1, 3] [3, 1]
    reflectedRecipe374

theorem reflectedGram329_check : reflectedEntryCheck reflectedGram329.2 = true := by decide +kernel

def reflectedGram330 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [2, 3, 1] [1, 2, 3, 0]
    reflectedRecipe36

theorem reflectedGram330_check : reflectedEntryCheck reflectedGram330.2 = true := by decide +kernel

def reflectedGram331 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [2, 3, 1] [1, 3, 2, 0]
    reflectedRecipe151

theorem reflectedGram331_check : reflectedEntryCheck reflectedGram331.2 = true := by decide +kernel

def reflectedGram332 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 3, 1] [2, 1, 3, 0]
    reflectedRecipe204

theorem reflectedGram332_check : reflectedEntryCheck reflectedGram332.2 = true := by decide +kernel

def reflectedGram333 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [2, 3, 1] [2, 3, 1, 0]
    reflectedRecipe251

theorem reflectedGram333_check : reflectedEntryCheck reflectedGram333.2 = true := by decide +kernel

def reflectedGram334 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 3, 1] [3, 1, 2, 0]
    reflectedRecipe275

theorem reflectedGram334_check : reflectedEntryCheck reflectedGram334.2 = true := by decide +kernel

def reflectedGram335 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [2, 3, 1] [3, 2, 1, 0]
    reflectedRecipe289

theorem reflectedGram335_check : reflectedEntryCheck reflectedGram335.2 = true := by decide +kernel

def reflectedGram336 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [2, 3, 1] [1, 2, 3, 1]
    reflectedRecipe154

theorem reflectedGram336_check : reflectedEntryCheck reflectedGram336.2 = true := by decide +kernel

def reflectedGram337 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [2, 3, 1] [1, 3, 2, 1]
    reflectedRecipe319

theorem reflectedGram337_check : reflectedEntryCheck reflectedGram337.2 = true := by decide +kernel

def reflectedGram338 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 3, 1] [2, 1, 3, 2]
    reflectedRecipe329

theorem reflectedGram338_check : reflectedEntryCheck reflectedGram338.2 = true := by decide +kernel

def reflectedGram339 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 3, 1] [2, 3, 1, 2]
    reflectedRecipe340

theorem reflectedGram339_check : reflectedEntryCheck reflectedGram339.2 = true := by decide +kernel

def reflectedGram340 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [2, 3, 1] [3, 1, 2, 3]
    reflectedRecipe355

theorem reflectedGram340_check : reflectedEntryCheck reflectedGram340.2 = true := by decide +kernel

def reflectedGram341 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [2, 3, 1] [3, 2, 1, 3]
    reflectedRecipe368

theorem reflectedGram341_check : reflectedEntryCheck reflectedGram341.2 = true := by decide +kernel

def reflectedGram342 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [2, 3, 1] [1, 2, 3]
    reflectedRecipe154

theorem reflectedGram342_check : reflectedEntryCheck reflectedGram342.2 = true := by decide +kernel

def reflectedGram343 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [2, 3, 1] [1, 3, 2]
    reflectedRecipe345

theorem reflectedGram343_check : reflectedEntryCheck reflectedGram343.2 = true := by decide +kernel

def reflectedGram344 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [2, 3, 1] [2, 1, 3]
    (appendRecipe reflectedRecipe203 (⟨[], [mkD (1) 1 [2, 3] [2] 1 [3] (5) 18]⟩ : ReflectedRecipe))

theorem reflectedGram344_check : reflectedEntryCheck reflectedGram344.2 = true := by decide +kernel

def reflectedGram345 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [2, 3, 1] [2, 3, 1]
    reflectedRecipe375

theorem reflectedGram345_check : reflectedEntryCheck reflectedGram345.2 = true := by decide +kernel

def reflectedGram346 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [2, 3, 1] [3, 1, 2]
    reflectedRecipe222

theorem reflectedGram346_check : reflectedEntryCheck reflectedGram346.2 = true := by decide +kernel

def reflectedGram347 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [2, 3, 1] [3, 2, 1]
    reflectedRecipe69

theorem reflectedGram347_check : reflectedEntryCheck reflectedGram347.2 = true := by decide +kernel

def reflectedGram348 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [2, 3, 1] [2, 3]
    reflectedRecipe375

theorem reflectedGram348_check : reflectedEntryCheck reflectedGram348.2 = true := by decide +kernel

def reflectedGram349 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [2, 3, 1] [2, 1]
    reflectedRecipe64

theorem reflectedGram349_check : reflectedEntryCheck reflectedGram349.2 = true := by decide +kernel

def reflectedGram350 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [2, 3, 1] [3, 2]
    reflectedRecipe179

theorem reflectedGram350_check : reflectedEntryCheck reflectedGram350.2 = true := by decide +kernel

def reflectedGram351 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [2, 3, 1] [3, 1]
    reflectedRecipe198

theorem reflectedGram351_check : reflectedEntryCheck reflectedGram351.2 = true := by decide +kernel

def reflectedGram352 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [3, 1, 2] [1, 2, 3, 0]
    reflectedRecipe38

theorem reflectedGram352_check : reflectedEntryCheck reflectedGram352.2 = true := by decide +kernel

def reflectedGram353 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [3, 1, 2] [1, 3, 2, 0]
    reflectedRecipe142

theorem reflectedGram353_check : reflectedEntryCheck reflectedGram353.2 = true := by decide +kernel

def reflectedGram354 : ℚ × Entry :=
  reflectedGramEntry (21 : ℚ) [3, 1, 2] [2, 1, 3, 0]
    reflectedRecipe213

theorem reflectedGram354_check : reflectedEntryCheck reflectedGram354.2 = true := by decide +kernel

def reflectedGram355 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [3, 1, 2] [2, 3, 1, 0]
    reflectedRecipe254

theorem reflectedGram355_check : reflectedEntryCheck reflectedGram355.2 = true := by decide +kernel

def reflectedGram356 : ℚ × Entry :=
  reflectedGramEntry (-21 : ℚ) [3, 1, 2] [3, 1, 2, 0]
    reflectedRecipe273

theorem reflectedGram356_check : reflectedEntryCheck reflectedGram356.2 = true := by decide +kernel

def reflectedGram357 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [3, 1, 2] [3, 2, 1, 0]
    reflectedRecipe291

theorem reflectedGram357_check : reflectedEntryCheck reflectedGram357.2 = true := by decide +kernel

def reflectedGram358 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [3, 1, 2] [1, 2, 3, 1]
    reflectedRecipe306

theorem reflectedGram358_check : reflectedEntryCheck reflectedGram358.2 = true := by decide +kernel

def reflectedGram359 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [3, 1, 2] [1, 3, 2, 1]
    reflectedRecipe320

theorem reflectedGram359_check : reflectedEntryCheck reflectedGram359.2 = true := by decide +kernel

def reflectedGram360 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [3, 1, 2] [2, 1, 3, 2]
    reflectedRecipe331

theorem reflectedGram360_check : reflectedEntryCheck reflectedGram360.2 = true := by decide +kernel

def reflectedGram361 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [3, 1, 2] [2, 3, 1, 2]
    reflectedRecipe222

theorem reflectedGram361_check : reflectedEntryCheck reflectedGram361.2 = true := by decide +kernel

def reflectedGram362 : ℚ × Entry :=
  reflectedGramEntry (-42 : ℚ) [3, 1, 2] [3, 1, 2, 3]
    reflectedRecipe350

theorem reflectedGram362_check : reflectedEntryCheck reflectedGram362.2 = true := by decide +kernel

def reflectedGram363 : ℚ × Entry :=
  reflectedGramEntry (42 : ℚ) [3, 1, 2] [3, 2, 1, 3]
    reflectedRecipe369

theorem reflectedGram363_check : reflectedEntryCheck reflectedGram363.2 = true := by decide +kernel

def reflectedGram364 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [3, 1, 2] [1, 2, 3]
    reflectedRecipe84

theorem reflectedGram364_check : reflectedEntryCheck reflectedGram364.2 = true := by decide +kernel

def reflectedGram365 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [3, 1, 2] [1, 3, 2]
    reflectedRecipe169

theorem reflectedGram365_check : reflectedEntryCheck reflectedGram365.2 = true := by decide +kernel

def reflectedGram366 : ℚ × Entry :=
  reflectedGramEntry (-49 : ℚ) [3, 1, 2] [2, 1, 3]
    reflectedRecipe354

theorem reflectedGram366_check : reflectedEntryCheck reflectedGram366.2 = true := by decide +kernel

def reflectedGram367 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [3, 1, 2] [2, 3, 1]
    reflectedRecipe222

theorem reflectedGram367_check : reflectedEntryCheck reflectedGram367.2 = true := by decide +kernel

def reflectedGram368 : ℚ × Entry :=
  reflectedGramEntry (49 : ℚ) [3, 1, 2] [3, 1, 2]
    reflectedRecipe376

theorem reflectedGram368_check : reflectedEntryCheck reflectedGram368.2 = true := by decide +kernel

def reflectedGram369 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [3, 1, 2] [3, 2, 1]
    (appendRecipe reflectedRecipe239 (⟨[], [mkD (1) 1 [3, 1] [3] 2 [1] (5) 18]⟩ : ReflectedRecipe))

theorem reflectedGram369_check : reflectedEntryCheck reflectedGram369.2 = true := by decide +kernel

def reflectedGram370 : ℚ × Entry :=
  reflectedGramEntry (70/9 : ℚ) [3, 1, 2] [2, 3]
    reflectedRecipe178

theorem reflectedGram370_check : reflectedEntryCheck reflectedGram370.2 = true := by decide +kernel

def reflectedGram371 : ℚ × Entry :=
  reflectedGramEntry (-7/2 : ℚ) [3, 1, 2] [2, 1]
    reflectedRecipe377

theorem reflectedGram371_check : reflectedEntryCheck reflectedGram371.2 = true := by decide +kernel

def reflectedGram372 : ℚ × Entry :=
  reflectedGramEntry (-70/9 : ℚ) [3, 1, 2] [3, 2]
    reflectedRecipe87

theorem reflectedGram372_check : reflectedEntryCheck reflectedGram372.2 = true := by decide +kernel

def reflectedGram373 : ℚ × Entry :=
  reflectedGramEntry (7/2 : ℚ) [3, 1, 2] [3, 1]
    reflectedRecipe376

theorem reflectedGram373_check : reflectedEntryCheck reflectedGram373.2 = true := by decide +kernel

def reflectedGram374 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [3, 2, 1] [1, 2, 3, 0]
    reflectedRecipe39

theorem reflectedGram374_check : reflectedEntryCheck reflectedGram374.2 = true := by decide +kernel

def reflectedGram375 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [3, 2, 1] [1, 3, 2, 0]
    reflectedRecipe152

theorem reflectedGram375_check : reflectedEntryCheck reflectedGram375.2 = true := by decide +kernel

def reflectedGram376 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 2, 1] [2, 1, 3, 0]
    reflectedRecipe214

theorem reflectedGram376_check : reflectedEntryCheck reflectedGram376.2 = true := by decide +kernel

def reflectedGram377 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [3, 2, 1] [2, 3, 1, 0]
    reflectedRecipe243

theorem reflectedGram377_check : reflectedEntryCheck reflectedGram377.2 = true := by decide +kernel

def reflectedGram378 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 2, 1] [3, 1, 2, 0]
    reflectedRecipe265

theorem reflectedGram378_check : reflectedEntryCheck reflectedGram378.2 = true := by decide +kernel

def reflectedGram379 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [3, 2, 1] [3, 2, 1, 0]
    reflectedRecipe281

theorem reflectedGram379_check : reflectedEntryCheck reflectedGram379.2 = true := by decide +kernel

def reflectedGram380 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [3, 2, 1] [1, 2, 3, 1]
    reflectedRecipe307

theorem reflectedGram380_check : reflectedEntryCheck reflectedGram380.2 = true := by decide +kernel

def reflectedGram381 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [3, 2, 1] [1, 3, 2, 1]
    reflectedRecipe46

theorem reflectedGram381_check : reflectedEntryCheck reflectedGram381.2 = true := by decide +kernel

def reflectedGram382 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 2, 1] [2, 1, 3, 2]
    reflectedRecipe332

theorem reflectedGram382_check : reflectedEntryCheck reflectedGram382.2 = true := by decide +kernel

def reflectedGram383 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 2, 1] [2, 3, 1, 2]
    reflectedRecipe347

theorem reflectedGram383_check : reflectedEntryCheck reflectedGram383.2 = true := by decide +kernel

def reflectedGram384 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [3, 2, 1] [3, 1, 2, 3]
    reflectedRecipe356

theorem reflectedGram384_check : reflectedEntryCheck reflectedGram384.2 = true := by decide +kernel

def reflectedGram385 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [3, 2, 1] [3, 2, 1, 3]
    reflectedRecipe364

theorem reflectedGram385_check : reflectedEntryCheck reflectedGram385.2 = true := by decide +kernel

def reflectedGram386 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [3, 2, 1] [1, 2, 3]
    reflectedRecipe366

theorem reflectedGram386_check : reflectedEntryCheck reflectedGram386.2 = true := by decide +kernel

def reflectedGram387 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [3, 2, 1] [1, 3, 2]
    reflectedRecipe46

theorem reflectedGram387_check : reflectedEntryCheck reflectedGram387.2 = true := by decide +kernel

def reflectedGram388 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [3, 2, 1] [2, 1, 3]
    reflectedRecipe236

theorem reflectedGram388_check : reflectedEntryCheck reflectedGram388.2 = true := by decide +kernel

def reflectedGram389 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [3, 2, 1] [2, 3, 1]
    reflectedRecipe179

theorem reflectedGram389_check : reflectedEntryCheck reflectedGram389.2 = true := by decide +kernel

def reflectedGram390 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [3, 2, 1] [3, 1, 2]
    (appendRecipe reflectedRecipe239 (⟨[], [mkD (1) 1 [3, 2] [3] 1 [2] (5) 18]⟩ : ReflectedRecipe))

theorem reflectedGram390_check : reflectedEntryCheck reflectedGram390.2 = true := by decide +kernel

def reflectedGram391 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [3, 2, 1] [3, 2, 1]
    reflectedRecipe378

theorem reflectedGram391_check : reflectedEntryCheck reflectedGram391.2 = true := by decide +kernel

def reflectedGram392 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [3, 2, 1] [2, 3]
    reflectedRecipe69

theorem reflectedGram392_check : reflectedEntryCheck reflectedGram392.2 = true := by decide +kernel

def reflectedGram393 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [3, 2, 1] [2, 1]
    reflectedRecipe103

theorem reflectedGram393_check : reflectedEntryCheck reflectedGram393.2 = true := by decide +kernel

def reflectedGram394 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [3, 2, 1] [3, 2]
    reflectedRecipe378

theorem reflectedGram394_check : reflectedEntryCheck reflectedGram394.2 = true := by decide +kernel

def reflectedGram395 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [3, 2, 1] [3, 1]
    reflectedRecipe87

theorem reflectedGram395_check : reflectedEntryCheck reflectedGram395.2 = true := by decide +kernel

def reflectedGram396 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [2, 3] [1, 2, 3, 0]
    reflectedRecipe100

theorem reflectedGram396_check : reflectedEntryCheck reflectedGram396.2 = true := by decide +kernel

def reflectedGram397 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [2, 3] [1, 3, 2, 0]
    reflectedRecipe192

theorem reflectedGram397_check : reflectedEntryCheck reflectedGram397.2 = true := by decide +kernel

def reflectedGram398 : ℚ × Entry :=
  reflectedGramEntry (10/3 : ℚ) [2, 3] [2, 1, 3, 0]
    reflectedRecipe238

theorem reflectedGram398_check : reflectedEntryCheck reflectedGram398.2 = true := by decide +kernel

def reflectedGram399 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [2, 3] [2, 3, 1, 0]
    reflectedRecipe73

theorem reflectedGram399_check : reflectedEntryCheck reflectedGram399.2 = true := by decide +kernel

def reflectedGram400 : ℚ × Entry :=
  reflectedGramEntry (-10/3 : ℚ) [2, 3] [3, 1, 2, 0]
    reflectedRecipe279

theorem reflectedGram400_check : reflectedEntryCheck reflectedGram400.2 = true := by decide +kernel

def reflectedGram401 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [2, 3] [3, 2, 1, 0]
    reflectedRecipe296

theorem reflectedGram401_check : reflectedEntryCheck reflectedGram401.2 = true := by decide +kernel

def reflectedGram402 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [2, 3] [1, 2, 3, 1]
    reflectedRecipe154

theorem reflectedGram402_check : reflectedEntryCheck reflectedGram402.2 = true := by decide +kernel

def reflectedGram403 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [2, 3] [1, 3, 2, 1]
    reflectedRecipe321

theorem reflectedGram403_check : reflectedEntryCheck reflectedGram403.2 = true := by decide +kernel

def reflectedGram404 : ℚ × Entry :=
  reflectedGramEntry (20/3 : ℚ) [2, 3] [2, 1, 3, 2]
    reflectedRecipe334

theorem reflectedGram404_check : reflectedEntryCheck reflectedGram404.2 = true := by decide +kernel

def reflectedGramBlock5 : List (ℚ × Entry) :=
  [reflectedGram324,
  reflectedGram325,
  reflectedGram326,
  reflectedGram327,
  reflectedGram328,
  reflectedGram329,
  reflectedGram330,
  reflectedGram331,
  reflectedGram332,
  reflectedGram333,
  reflectedGram334,
  reflectedGram335,
  reflectedGram336,
  reflectedGram337,
  reflectedGram338,
  reflectedGram339,
  reflectedGram340,
  reflectedGram341,
  reflectedGram342,
  reflectedGram343,
  reflectedGram344,
  reflectedGram345,
  reflectedGram346,
  reflectedGram347,
  reflectedGram348,
  reflectedGram349,
  reflectedGram350,
  reflectedGram351,
  reflectedGram352,
  reflectedGram353,
  reflectedGram354,
  reflectedGram355,
  reflectedGram356,
  reflectedGram357,
  reflectedGram358,
  reflectedGram359,
  reflectedGram360,
  reflectedGram361,
  reflectedGram362,
  reflectedGram363,
  reflectedGram364,
  reflectedGram365,
  reflectedGram366,
  reflectedGram367,
  reflectedGram368,
  reflectedGram369,
  reflectedGram370,
  reflectedGram371,
  reflectedGram372,
  reflectedGram373,
  reflectedGram374,
  reflectedGram375,
  reflectedGram376,
  reflectedGram377,
  reflectedGram378,
  reflectedGram379,
  reflectedGram380,
  reflectedGram381,
  reflectedGram382,
  reflectedGram383,
  reflectedGram384,
  reflectedGram385,
  reflectedGram386,
  reflectedGram387,
  reflectedGram388,
  reflectedGram389,
  reflectedGram390,
  reflectedGram391,
  reflectedGram392,
  reflectedGram393,
  reflectedGram394,
  reflectedGram395,
  reflectedGram396,
  reflectedGram397,
  reflectedGram398,
  reflectedGram399,
  reflectedGram400,
  reflectedGram401,
  reflectedGram402,
  reflectedGram403,
  reflectedGram404]

theorem reflectedGramBlock5_check :
    reflectedGramBlock5.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramBlock5, List.all_cons, List.all_nil, Bool.and_true,
    reflectedGram324_check,
    reflectedGram325_check,
    reflectedGram326_check,
    reflectedGram327_check,
    reflectedGram328_check,
    reflectedGram329_check,
    reflectedGram330_check,
    reflectedGram331_check,
    reflectedGram332_check,
    reflectedGram333_check,
    reflectedGram334_check,
    reflectedGram335_check,
    reflectedGram336_check,
    reflectedGram337_check,
    reflectedGram338_check,
    reflectedGram339_check,
    reflectedGram340_check,
    reflectedGram341_check,
    reflectedGram342_check,
    reflectedGram343_check,
    reflectedGram344_check,
    reflectedGram345_check,
    reflectedGram346_check,
    reflectedGram347_check,
    reflectedGram348_check,
    reflectedGram349_check,
    reflectedGram350_check,
    reflectedGram351_check,
    reflectedGram352_check,
    reflectedGram353_check,
    reflectedGram354_check,
    reflectedGram355_check,
    reflectedGram356_check,
    reflectedGram357_check,
    reflectedGram358_check,
    reflectedGram359_check,
    reflectedGram360_check,
    reflectedGram361_check,
    reflectedGram362_check,
    reflectedGram363_check,
    reflectedGram364_check,
    reflectedGram365_check,
    reflectedGram366_check,
    reflectedGram367_check,
    reflectedGram368_check,
    reflectedGram369_check,
    reflectedGram370_check,
    reflectedGram371_check,
    reflectedGram372_check,
    reflectedGram373_check,
    reflectedGram374_check,
    reflectedGram375_check,
    reflectedGram376_check,
    reflectedGram377_check,
    reflectedGram378_check,
    reflectedGram379_check,
    reflectedGram380_check,
    reflectedGram381_check,
    reflectedGram382_check,
    reflectedGram383_check,
    reflectedGram384_check,
    reflectedGram385_check,
    reflectedGram386_check,
    reflectedGram387_check,
    reflectedGram388_check,
    reflectedGram389_check,
    reflectedGram390_check,
    reflectedGram391_check,
    reflectedGram392_check,
    reflectedGram393_check,
    reflectedGram394_check,
    reflectedGram395_check,
    reflectedGram396_check,
    reflectedGram397_check,
    reflectedGram398_check,
    reflectedGram399_check,
    reflectedGram400_check,
    reflectedGram401_check,
    reflectedGram402_check,
    reflectedGram403_check,
    reflectedGram404_check]

end AlbertSequential.FiveTest
