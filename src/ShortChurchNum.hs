{- |
  Module      : ShortChurchNum
  Description : Church encodeした自然数 (0～256)
-}

module ShortChurchNum where

-- | コンパクトにChurch encodeした自然数 (0～256)
shortChNum :: [String]
shortChNum = [
      "`ki"                                                              --   0
    , "i"                                                                --   1
    , "` `s``s`ksk i"                                                    --   2
    , "``s`k```ss`s`sisk"                                                --   3
    , "` ``sii ` `s``s`ksk i"                                            --   4
    , "` `s``s`ksk ` ``sii ` `s``s`ksk i"                                --   5
    , "` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"                    --   6
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"        --   7
    , "` ``s`k```ss`s`sisk ` `s``s`ksk i"                                --   8
    , "` ` `s``s`ksk i ``s`k```ss`s`sisk"                                --   9
    , "` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"                    --  10
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"        --  11
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"               --  12
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"   --  13
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"   --  15
    , "```s`sii``s``s`kski"                                              --  16
    , "` `s``s`ksk ```s`sii``s``s`kski"                                  --  17
    , "` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"                      --  18
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"          --  19
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk i"   --  24
    , "` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"                --  25
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"    --  26
    , "` ``sii ``s`k```ss`s`sisk"                                        --  27
    , "` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"                            --  28
    , "` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"                --  29
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"    --  30
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"                --  32
    , "` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"    --  33
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"         --  34
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"    --  36
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk" --  43
    , "` `s``s`ksk `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"                 --  48
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"     --  49
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"     --  51
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"               --  54
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"   --  55
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"   --  56
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"                        --  64
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"            --  65
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski" --  68
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski" --  80
    , "` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"                        --  81
    , "` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"            --  82
    , "` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"
    , "` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"    -- 100
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"       -- 108
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"            -- 125
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ` `s``s`ksk i ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``si`k`s``s`ksk ```s`sii``s``s`kski `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i `` ``si`k`s``s`ksk ` ``sii ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i `` ``si`k`s``s`ksk ```s`sii``s``s`kski ` ``sii ``s`k```ss`s`sisk"
    , "` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i `` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk i"
    , "`` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ` `s``s`ksk i ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk ` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "` `s``s`ksk `` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ```s`sii``s``s`kski"
    , "`` ``s`ksk ` `s``s`ksk i ` ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"            -- 243
    , "` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk ` `s``s`ksk ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``si`k`s``s`ksk ` ``sii ` `s``s`ksk i ` ` `s``s`ksk ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ``s`k```ss`s`sisk ` `s``s`ksk ` `s``s`ksk ` ` ``sii ` `s``s`ksk i ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "` `s``s`ksk `` ``s`ksk ` `s``s`ksk i ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "` `s``s`ksk `` ``s`ksk ` ` `s``s`ksk i ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ``s`k```ss`s`sisk"
    , "`` ``s`ksk ` `s``s`ksk i ` `s``s`ksk ` `s``s`ksk ` ``s`k```ss`s`sisk ` `s``s`ksk ` ``sii ` `s``s`ksk i"
    , "`` ``s`ksk ``s`k```ss`s`sisk `` ``s`ksk ` `s``s`ksk ` ``sii ` `s``s`ksk i ` `s``s`ksk ```s`sii``s``s`kski"
    , "```sii```sii``s``s`kski"                                          -- 256
    ]
