% -----------------------------------------------------------------------------
% $Id: CPUTime.lhs,v 1.28 2001/02/22 13:17:58 simonpj Exp $
%
% (c) The University of Glasgow, 1995-2000
%
\section[CPUTime]{Haskell 98 CPU Time Library}

\begin{code}
{-# OPTIONS -#include "cbits/stgio.h" #-}

module CPUTime 
	(
         getCPUTime,       -- :: IO Integer
	 cpuTimePrecision  -- :: Integer
        ) where
\end{code}


#ifndef __HUGS__

\begin{code}
import Prelude		-- To generate the dependency
import PrelGHC		( indexIntArray# )
import PrelBase		( Int(..) )
import PrelByteArr  	( ByteArray(..), newIntArray )
import PrelArrExtra     ( unsafeFreezeByteArray )
import PrelNum		( fromInt )
import PrelIOBase	( IOException(..), 
			  IOErrorType( UnsupportedOperation ), 
			  unsafePerformIO, stToIO, ioException )
import Ratio
\end{code}

Computation @getCPUTime@ returns the number of picoseconds CPU time
used by the current program.  The precision of this result is
implementation-dependent.

The @cpuTimePrecision@ constant is the smallest measurable difference
in CPU time that the implementation can record, and is given as an
integral number of picoseconds.

\begin{code}
getCPUTime :: IO Integer
getCPUTime = do
    marr <- stToIO (newIntArray ((0::Int),3))
    barr <- stToIO (unsafeFreezeByteArray marr)
    rc   <- primGetCPUTime barr
    if rc /= 0 then
      case barr of
       ByteArray _ _ frozen# -> -- avoid bounds checking
        return ((fromIntegral (I# (indexIntArray# frozen# 0#)) * 1000000000 + 
                 fromIntegral (I# (indexIntArray# frozen# 1#)) + 
		 fromIntegral (I# (indexIntArray# frozen# 2#)) * 1000000000 + 
                 fromIntegral (I# (indexIntArray# frozen# 3#))) * 1000)
     else
	ioException (IOError Nothing UnsupportedOperation 
			 "getCPUTime"
		         "can't get CPU time"
			 Nothing)

cpuTimePrecision :: Integer
cpuTimePrecision = round ((1000000000000::Integer) % 
                          fromIntegral (unsafePerformIO clockTicks))

foreign import "libHS_cbits" "getCPUTime" unsafe primGetCPUTime :: ByteArray Int -> IO Int
foreign import "libHS_cbits" "clockTicks" unsafe clockTicks :: IO Int

\end{code}

#else

\begin{code}
import PrelPrim ( nh_getCPUtime
		, nh_getCPUprec
		, unsafePerformIO
		)

getCPUTime :: IO Integer
getCPUTime 
   = do seconds <- nh_getCPUtime
        return (round (seconds * 1.0e+12))

cpuTimePrecision :: Integer
cpuTimePrecision
   = unsafePerformIO (
        do resolution <- nh_getCPUprec
           return (round (resolution * 1.0e+12))
     )
\end{code} 
#endif
