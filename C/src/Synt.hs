{-# OPTIONS_GHC -w #-}
module Synt where
import Grammar
import Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.12

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12

happyExpList :: Happy_Data_Array.Array Int Int
happyExpList = Happy_Data_Array.listArray (0,132) ([12288,1110,50688,138,512,0,0,0,0,0,0,0,0,0,12,0,2,0,1,0,0,0,25344,69,44128,8,4,32768,0,0,0,0,0,0,0,11032,2,17763,0,64,0,8,16384,0,34816,1,0,0,0,2048,514,16640,64,2080,8,5516,1,0,0,512,33280,128,0,4,0,4,0,0,0,35840,277,45440,34,0,0,0,0,0,0,0,32768,16,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_synt","Exp","Dis","Con","Un","Variable","Pred","Term","Add","Mult","var","pr","\"->\"","'|'","'&'","'!'","'('","')'","'@'","'.'","'?'","'='","'+'","'*'","'0'","kav","%eof"]
        bit_start = st * 29
        bit_end = (st + 1) * 29
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..28]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

action_0 (13) = happyShift action_10
action_0 (14) = happyShift action_11
action_0 (18) = happyShift action_12
action_0 (19) = happyShift action_13
action_0 (21) = happyShift action_14
action_0 (23) = happyShift action_15
action_0 (27) = happyShift action_16
action_0 (4) = happyGoto action_17
action_0 (5) = happyGoto action_18
action_0 (6) = happyGoto action_3
action_0 (7) = happyGoto action_4
action_0 (8) = happyGoto action_5
action_0 (9) = happyGoto action_6
action_0 (10) = happyGoto action_7
action_0 (11) = happyGoto action_8
action_0 (12) = happyGoto action_9
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (13) = happyShift action_10
action_1 (14) = happyShift action_11
action_1 (18) = happyShift action_12
action_1 (19) = happyShift action_13
action_1 (21) = happyShift action_14
action_1 (23) = happyShift action_15
action_1 (27) = happyShift action_16
action_1 (5) = happyGoto action_2
action_1 (6) = happyGoto action_3
action_1 (7) = happyGoto action_4
action_1 (8) = happyGoto action_5
action_1 (9) = happyGoto action_6
action_1 (10) = happyGoto action_7
action_1 (11) = happyGoto action_8
action_1 (12) = happyGoto action_9
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (16) = happyShift action_20
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (17) = happyShift action_30
action_3 _ = happyReduce_3

action_4 _ = happyReduce_5

action_5 _ = happyReduce_19

action_6 _ = happyReduce_7

action_7 (24) = happyShift action_28
action_7 (25) = happyShift action_29
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (26) = happyShift action_27
action_8 _ = happyReduce_15

action_9 (28) = happyShift action_26
action_9 _ = happyReduce_17

action_10 _ = happyReduce_12

action_11 _ = happyReduce_13

action_12 (13) = happyShift action_10
action_12 (14) = happyShift action_11
action_12 (18) = happyShift action_12
action_12 (19) = happyShift action_13
action_12 (21) = happyShift action_14
action_12 (23) = happyShift action_15
action_12 (27) = happyShift action_16
action_12 (7) = happyGoto action_25
action_12 (8) = happyGoto action_5
action_12 (9) = happyGoto action_6
action_12 (10) = happyGoto action_7
action_12 (11) = happyGoto action_8
action_12 (12) = happyGoto action_9
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (13) = happyShift action_10
action_13 (14) = happyShift action_11
action_13 (18) = happyShift action_12
action_13 (19) = happyShift action_13
action_13 (21) = happyShift action_14
action_13 (23) = happyShift action_15
action_13 (27) = happyShift action_16
action_13 (4) = happyGoto action_23
action_13 (5) = happyGoto action_18
action_13 (6) = happyGoto action_3
action_13 (7) = happyGoto action_4
action_13 (8) = happyGoto action_5
action_13 (9) = happyGoto action_6
action_13 (10) = happyGoto action_24
action_13 (11) = happyGoto action_8
action_13 (12) = happyGoto action_9
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (13) = happyShift action_10
action_14 (8) = happyGoto action_22
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (13) = happyShift action_10
action_15 (8) = happyGoto action_21
action_15 _ = happyFail (happyExpListPerState 15)

action_16 _ = happyReduce_21

action_17 (29) = happyAccept
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (15) = happyShift action_19
action_18 (16) = happyShift action_20
action_18 _ = happyReduce_1

action_19 (13) = happyShift action_10
action_19 (14) = happyShift action_11
action_19 (18) = happyShift action_12
action_19 (19) = happyShift action_13
action_19 (21) = happyShift action_14
action_19 (23) = happyShift action_15
action_19 (27) = happyShift action_16
action_19 (4) = happyGoto action_41
action_19 (5) = happyGoto action_18
action_19 (6) = happyGoto action_3
action_19 (7) = happyGoto action_4
action_19 (8) = happyGoto action_5
action_19 (9) = happyGoto action_6
action_19 (10) = happyGoto action_7
action_19 (11) = happyGoto action_8
action_19 (12) = happyGoto action_9
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (13) = happyShift action_10
action_20 (14) = happyShift action_11
action_20 (18) = happyShift action_12
action_20 (19) = happyShift action_13
action_20 (21) = happyShift action_14
action_20 (23) = happyShift action_15
action_20 (27) = happyShift action_16
action_20 (6) = happyGoto action_40
action_20 (7) = happyGoto action_4
action_20 (8) = happyGoto action_5
action_20 (9) = happyGoto action_6
action_20 (10) = happyGoto action_7
action_20 (11) = happyGoto action_8
action_20 (12) = happyGoto action_9
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (22) = happyShift action_39
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (22) = happyShift action_38
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (20) = happyShift action_37
action_23 _ = happyFail (happyExpListPerState 23)

action_24 (20) = happyShift action_36
action_24 (24) = happyShift action_28
action_24 (25) = happyShift action_29
action_24 _ = happyFail (happyExpListPerState 24)

action_25 _ = happyReduce_8

action_26 _ = happyReduce_22

action_27 (13) = happyShift action_10
action_27 (19) = happyShift action_33
action_27 (27) = happyShift action_16
action_27 (8) = happyGoto action_5
action_27 (12) = happyGoto action_35
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (13) = happyShift action_10
action_28 (19) = happyShift action_33
action_28 (27) = happyShift action_16
action_28 (8) = happyGoto action_5
action_28 (10) = happyGoto action_34
action_28 (11) = happyGoto action_8
action_28 (12) = happyGoto action_9
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (13) = happyShift action_10
action_29 (19) = happyShift action_33
action_29 (27) = happyShift action_16
action_29 (8) = happyGoto action_5
action_29 (11) = happyGoto action_32
action_29 (12) = happyGoto action_9
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (13) = happyShift action_10
action_30 (14) = happyShift action_11
action_30 (18) = happyShift action_12
action_30 (19) = happyShift action_13
action_30 (21) = happyShift action_14
action_30 (23) = happyShift action_15
action_30 (27) = happyShift action_16
action_30 (7) = happyGoto action_31
action_30 (8) = happyGoto action_5
action_30 (9) = happyGoto action_6
action_30 (10) = happyGoto action_7
action_30 (11) = happyGoto action_8
action_30 (12) = happyGoto action_9
action_30 _ = happyFail (happyExpListPerState 30)

action_31 _ = happyReduce_6

action_32 (26) = happyShift action_27
action_32 _ = happyReduce_16

action_33 (13) = happyShift action_10
action_33 (19) = happyShift action_33
action_33 (27) = happyShift action_16
action_33 (8) = happyGoto action_5
action_33 (10) = happyGoto action_44
action_33 (11) = happyGoto action_8
action_33 (12) = happyGoto action_9
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (25) = happyShift action_29
action_34 _ = happyReduce_14

action_35 (28) = happyShift action_26
action_35 _ = happyReduce_18

action_36 _ = happyReduce_20

action_37 _ = happyReduce_9

action_38 (13) = happyShift action_10
action_38 (14) = happyShift action_11
action_38 (18) = happyShift action_12
action_38 (19) = happyShift action_13
action_38 (21) = happyShift action_14
action_38 (23) = happyShift action_15
action_38 (27) = happyShift action_16
action_38 (4) = happyGoto action_43
action_38 (5) = happyGoto action_18
action_38 (6) = happyGoto action_3
action_38 (7) = happyGoto action_4
action_38 (8) = happyGoto action_5
action_38 (9) = happyGoto action_6
action_38 (10) = happyGoto action_7
action_38 (11) = happyGoto action_8
action_38 (12) = happyGoto action_9
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (13) = happyShift action_10
action_39 (14) = happyShift action_11
action_39 (18) = happyShift action_12
action_39 (19) = happyShift action_13
action_39 (21) = happyShift action_14
action_39 (23) = happyShift action_15
action_39 (27) = happyShift action_16
action_39 (4) = happyGoto action_42
action_39 (5) = happyGoto action_18
action_39 (6) = happyGoto action_3
action_39 (7) = happyGoto action_4
action_39 (8) = happyGoto action_5
action_39 (9) = happyGoto action_6
action_39 (10) = happyGoto action_7
action_39 (11) = happyGoto action_8
action_39 (12) = happyGoto action_9
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (17) = happyShift action_30
action_40 _ = happyReduce_4

action_41 _ = happyReduce_2

action_42 _ = happyReduce_11

action_43 _ = happyReduce_10

action_44 (20) = happyShift action_36
action_44 (25) = happyShift action_29
action_44 _ = happyFail (happyExpListPerState 44)

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn4  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (Impl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  5 happyReduction_3
happyReduction_3 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_3  5 happyReduction_4
happyReduction_4 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (Or happy_var_1 happy_var_3
	)
happyReduction_4 _ _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  6 happyReduction_5
happyReduction_5 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_1
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  6 happyReduction_6
happyReduction_6 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (And happy_var_1 happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_1  7 happyReduction_7
happyReduction_7 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn7
		 (Expr happy_var_1
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_2  7 happyReduction_8
happyReduction_8 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (Not happy_var_2
	)
happyReduction_8 _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  7 happyReduction_9
happyReduction_9 _
	(HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (happy_var_2
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 4 7 happyReduction_10
happyReduction_10 ((HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 (ForAll happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 4 7 happyReduction_11
happyReduction_11 ((HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 (Exists happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_1  8 happyReduction_12
happyReduction_12 (HappyTerminal (MVar happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  9 happyReduction_13
happyReduction_13 (HappyTerminal (MPr happy_var_1))
	 =  HappyAbsSyn9
		 (Pred happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  9 happyReduction_14
happyReduction_14 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 (Eq happy_var_1 happy_var_3
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  10 happyReduction_15
happyReduction_15 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  10 happyReduction_16
happyReduction_16 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Sum happy_var_1 happy_var_3
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  11 happyReduction_17
happyReduction_17 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  11 happyReduction_18
happyReduction_18 (HappyAbsSyn12  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Mul happy_var_1 happy_var_3
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  12 happyReduction_19
happyReduction_19 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn12
		 (Term happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_3  12 happyReduction_20
happyReduction_20 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (happy_var_2
	)
happyReduction_20 _ _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  12 happyReduction_21
happyReduction_21 _
	 =  HappyAbsSyn12
		 (Zero
	)

happyReduce_22 = happySpecReduce_2  12 happyReduction_22
happyReduction_22 _
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (Next happy_var_1
	)
happyReduction_22 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 29 29 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	MVar happy_dollar_dollar -> cont 13;
	MPr happy_dollar_dollar -> cont 14;
	MImpl -> cont 15;
	MOr -> cont 16;
	MAnd -> cont 17;
	MNot -> cont 18;
	MOpen -> cont 19;
	MClose -> cont 20;
	MForAll -> cont 21;
	MPoint -> cont 22;
	MExists -> cont 23;
	MEq -> cont 24;
	MSum -> cont 25;
	MMul -> cont 26;
	MZero -> cont 27;
	MNext -> cont 28;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 29 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [String]) -> HappyIdentity a
happyError' = HappyIdentity . (\(tokens, _) -> parseError tokens)
synt tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Parse error"
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x < y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `div` 16)) (bit `mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
