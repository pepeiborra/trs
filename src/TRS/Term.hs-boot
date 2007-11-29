module TRS.Term where

import TRS.Types

class Term (t :: (* -> *) -> *) (s :: * -> *) (user :: *) | t -> user
