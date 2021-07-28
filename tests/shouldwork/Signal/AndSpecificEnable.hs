module AndSpecificEnable where

import Clash.Prelude

import qualified Clash.Explicit.Prelude as CEP
import Clash.Explicit.Testbench

createDomain vSystem{vName="SystemSlow", vPeriod=2 * vPeriod vSystem}

topEntity
  :: Clock System
  -> Clock SystemSlow
  -> Reset System
  -> Reset SystemSlow
  -> Enable System
  -> Enable SystemSlow
  -> Signal SystemSlow Bool
  -> Signal System (Unsigned 8)
  -> Signal SystemSlow (Unsigned 8)
  -> (Signal System (Unsigned 8), Signal SystemSlow (Unsigned 8, Unsigned 8))
topEntity clk1 clk2 rst1 rst2 en1 en2 enM =
  let f :: HiddenClockResetEnable dom
        => Signal dom Bool
        -> Signal dom (Unsigned 8)
        -> Signal dom (Unsigned 8, Unsigned 8)
      f enM0 i = bundle (register 0 i, andSpecificEnable enM0 $ register 0 i)
  in withClockResetEnable clk rst en (f enM)

f :: forall dom1 dom2
   . ( HiddenClockResetEnable dom1
     , HiddenClockResetEnable dom2)
  => Signal dom2 Bool
  -> Signal dom1 (Unsigned 8)
  -> Signal dom2 (Unsigned 8)
  -> (Signal dom1 (Unsigned 8), Signal dom2 (Unsigned 8, Unsigned 8))
f enM i1 i2 = (o1, o2)
 where
  (o1, o2_2) = andSpecificEnable @dom2 enM $ f0 i1 i2
  o2_1 = register 0 i
  o2 = bundle (o2_1, o2_2)

f0
  :: ( HiddenClockResetEnable dom1
     , HiddenClockResetEnable dom2)
  => Signal dom1 (Unsigned 8)
  -> Signal dom2 (Unsigned 8)
  -> (Signal dom1 (Unsigned 8), Signal dom2 (Unsigned 8))
f0 i1 i2 = (register 0 i1, register 0 i2)

testBench
  :: Signal System Bool
testBench = done
 where
  en  = True :> True :> False :> True :> True  :> True :> False :> True :> Nil
  enM = True :> True :> False :> True :> False :> True :> Nil
  en0 = toEnable $ stimuliGenerator clk rst en
  enM0 = stimuliGenerator clk rst enM
  inp = CEP.delay clk enableGen 0 $ inp + 1
  expectedOutput = outputVerifier clk rst
    $    (0, 0) :> (1, 1) :> (2, 2) :> (2, 2) :> (4, 4) :>  (5, 4) :> (6, 6)
      :> (6, 6) :> (8, 8) :> Nil
  done = expectedOutput $ topEntity clk rst en0 enM0 inp
  clk = tbSystemClockGen (not <$> done)
  rst = systemResetGen
