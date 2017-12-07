module AST

%default total
%access public export

-- Abstract Syntax --

-- Literals
data Lit = LitInt String | IntType
  -- deriving (Show,Eq)

Eq Lit where
  (LitInt s1) == (LitInt s2) = s1 == s2
  IntType == IntType = True
  _ == _ = False

-- Sorts
data Sort = Star | Box | SortNum Int
  -- deriving (Show,Eq)

Eq Sort where
  Star == Star = True
  Box == Box = True
  (SortNum i1) == (SortNum i2) = i1 == i2
  _ == _ = False

-- Variable
data Variable = Var String | Anonymous
  -- deriving (Show,Eq)

Eq Variable where
  (Var x) == (Var y) = x == y
  Anonymous == Anonymous = True
  _ == _ = False

mutual
  -- Typed Variable
  data TVariable = TVar Variable Expr
  -- deriving (Show,Eq)

  -- Expression
  data Expr
    = LamExpr TVariable Expr          -- Lambda Abstraction
    | PiExpr TVariable Expr           -- Pi
    | AppExpr Expr Expr               -- Application
    | CaseExpr Expr (List Alt) Expr   -- Case
    | VarExpr TVariable               -- Typed Variable
    | LitExpr Lit                     -- Literal
    | SortExpr Sort                   -- Sorts
    | Unknown                         -- for untyped variables

  -- Type Constructor
  TCons : Type
  TCons = TVariable

  -- Data Constructor
  DCons : Type
  DCons = TVariable

  -- type constructor argument
  TCA : Type
  TCA = TVariable
  -- data constructor argument
  DCA : Type
  DCA = TVariable


  -- Case Alternative
  data Alt = MKAlt TCons (List TCA) (List DCA) Expr
    --deriving (Show,Eq)

-- Data Type Declaration
data TDeclaration = TDecl TCons (List DCons)
  -- deriving (Show,Eq)

-- Value Declaration
data VDeclaration = VDecl TVariable Expr
  -- deriving (Show,Eq)

-- The Program
data Program = Prog (List TDeclaration) (List VDeclaration)
  -- deriving (Show,Eq)

Show Variable where
  show Anonymous = "<anon>"
  show (Var n) = n


mutual
  Show TVariable where
    show (TVar v e) = "(" ++ (show v) ++ " : " ++ (assert_total (show e)) ++ ")"

  Show Expr where
    show (LamExpr tv ex) = "(Lam " ++ (show tv) ++ (show ex) ++ ")"
    show (PiExpr tv ex) = "(Forall " ++ (show tv) ++ " -> " ++ (show ex) ++ ")"
    show (AppExpr e1 e2) = "(" ++ (show e1) ++ " " ++ (show e2) ++ ")"
    show (VarExpr v) = (show v)
    show (LitExpr IntType) = "Int"
    show (LitExpr (LitInt x)) = x
    show (SortExpr Star) = "*"
    show (SortExpr Box) = "||"
    show (SortExpr (SortNum i)) = "(SortNum " ++ (show i) ++ ")"
    show Unknown = "?"
    show (CaseExpr e alts tp) = "(case " ++ (show e) ++ "{ " ++ (show alts) ++ "} : " ++ (show tp) ++ " )"

  Show Alt where
    show (MKAlt tc tcs dcs e) = "Alt "
                                  ++ (assert_total (show tc))
                                  ++ " "
                                  ++ (assert_total (show tcs))
                                  ++ " "
                                  ++ (assert_total(show dcs))
                                  ++ " "
                                  ++ (assert_total (show e))

Show TDeclaration where
  show (TDecl tc dcs) = "data " ++ (show tc) ++ " = " ++ (show dcs)

Show VDeclaration where
  show (VDecl v e) = "let " ++ (show v) ++ " = " ++ (show e)
