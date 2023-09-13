use crate::formulas::{AuxVarType, EncodedFormula, FormulaType, LitType, VarType};

const INDEX_ENCODING_SHIFT: u8 = 6;
const TYPE_ENCODE_MASK: u8 = 0b0001_1111;
const CACHE_ENCODE_MASK: u8 = 0b0010_0000;
const LARGES_32_INDEX: u32 = 0xffff_ffff >> INDEX_ENCODING_SHIFT;

const ENCODING_TRUE: u8 = 0x01;
const ENCODING_FALSE: u8 = 0x02;
const ENCODING_POS_FF: u8 = 0x03;
const ENCODING_POS_AUX_CNF: u8 = 0x04;
const ENCODING_POS_AUX_CC: u8 = 0x05;
const ENCODING_POS_AUX_PB: u8 = 0x06;
const ENCODING_NEG_FF: u8 = 0x07;
const ENCODING_NEG_AUX_CNF: u8 = 0x08;
const ENCODING_NEG_AUX_CC: u8 = 0x09;
const ENCODING_NEG_AUX_PB: u8 = 0x0A;
const ENCODING_AND: u8 = 0x0B;
const ENCODING_OR: u8 = 0x0C;
const ENCODING_NOT: u8 = 0x0D;
const ENCODING_IMPL: u8 = 0x0E;
const ENCODING_EQUIV: u8 = 0x0F;
const ENCODING_CC: u8 = 0x10;
const ENCODING_PBC: u8 = 0x11;

const ENCODING_LARGE_CACHE: u8 = 0x20;

const fn header(ty: u8, large_cache: bool) -> u8 {
    if large_cache {
        ENCODING_LARGE_CACHE | ty
    } else {
        ty
    }
}

#[allow(clippy::cast_possible_truncation)]
const fn index_32(n: u64) -> u32 {
    (n as u32) << INDEX_ENCODING_SHIFT
}

const fn index_64(n: u64) -> u64 {
    n << INDEX_ENCODING_SHIFT
}

pub trait Encoding {
    fn encode(index: u64, formula: FormulaType, large_cache: bool) -> Self;
    fn index(self) -> u64;
    fn to_formula(self) -> EncodedFormula;
    #[allow(clippy::wrong_self_convention)]
    fn is_large_cache(self) -> bool;
    fn formula_type(self) -> FormulaType;
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Copy, Clone, Hash)]
pub struct SmallFormulaEncoding {
    pub encoding: u32,
}

impl SmallFormulaEncoding {
    pub const fn as_64(self) -> FormulaEncoding {
        extend_32(self)
    }
}

// TODO: additional idea: Store `Not` as a separate bit in the header. So F =
//      Not(F'), where F doesn't have that bit, but F' does. This would allow us
//      to preserve space by removing the Not Cache, but complicates the process
//      of inserting and reading formulas from the caches.
#[allow(clippy::cast_lossless)]
impl Encoding for SmallFormulaEncoding {
    fn encode(index: u64, ty: FormulaType, large_cache: bool) -> Self {
        use FormulaType::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        debug_assert!(!is_64_index(index));

        let encoding = match ty {
            True => header(ENCODING_TRUE, large_cache) as u32,
            False => header(ENCODING_FALSE, large_cache) as u32,
            And => header(ENCODING_AND, large_cache) as u32 | index_32(index),
            Or => header(ENCODING_OR, large_cache) as u32 | index_32(index),
            Not => header(ENCODING_NOT, large_cache) as u32 | index_32(index),
            Impl => header(ENCODING_IMPL, large_cache) as u32 | index_32(index),
            Equiv => header(ENCODING_EQUIV, large_cache) as u32 | index_32(index),
            Cc => header(ENCODING_CC, large_cache) as u32 | index_32(index),
            Pbc => header(ENCODING_PBC, large_cache) as u32 | index_32(index),
            Lit(LitType::Pos(VarType::FF)) => header(ENCODING_POS_FF, large_cache) as u32 | index_32(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::CNF))) => header(ENCODING_POS_AUX_CNF, large_cache) as u32 | index_32(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::CC))) => header(ENCODING_POS_AUX_CC, large_cache) as u32 | index_32(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::PB))) => header(ENCODING_POS_AUX_PB, large_cache) as u32 | index_32(index),
            Lit(LitType::Neg(VarType::FF)) => header(ENCODING_NEG_FF, large_cache) as u32 | index_32(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::CNF))) => header(ENCODING_NEG_AUX_CNF, large_cache) as u32 | index_32(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::CC))) => header(ENCODING_NEG_AUX_CC, large_cache) as u32 | index_32(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::PB))) => header(ENCODING_NEG_AUX_PB, large_cache) as u32 | index_32(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::TMP)) | LitType::Neg(VarType::Aux(AuxVarType::TMP))) => {
                panic!("Solver variables or temporary aux variables should not be encoded!")
            }
        };
        Self { encoding }
    }

    fn to_formula(self) -> EncodedFormula {
        let encoding = extend_32(self);

        EncodedFormula { encoding }
    }

    fn index(self) -> u64 {
        (self.encoding >> INDEX_ENCODING_SHIFT) as u64
    }

    #[allow(clippy::cast_possible_truncation)]
    fn is_large_cache(self) -> bool {
        (self.encoding as u8) & CACHE_ENCODE_MASK != 0
    }

    #[allow(clippy::cast_possible_truncation)]
    fn formula_type(self) -> FormulaType {
        match (self.encoding as u8) & TYPE_ENCODE_MASK {
            ENCODING_TRUE => FormulaType::True,
            ENCODING_FALSE => FormulaType::False,
            ENCODING_POS_FF => FormulaType::Lit(LitType::Pos(VarType::FF)),
            ENCODING_POS_AUX_CNF => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::CNF))),
            ENCODING_POS_AUX_CC => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::CC))),
            ENCODING_POS_AUX_PB => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::PB))),
            ENCODING_NEG_FF => FormulaType::Lit(LitType::Neg(VarType::FF)),
            ENCODING_NEG_AUX_CNF => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::CNF))),
            ENCODING_NEG_AUX_CC => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::CC))),
            ENCODING_NEG_AUX_PB => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::PB))),
            ENCODING_AND => FormulaType::And,
            ENCODING_OR => FormulaType::Or,
            ENCODING_NOT => FormulaType::Not,
            ENCODING_IMPL => FormulaType::Impl,
            ENCODING_EQUIV => FormulaType::Equiv,
            ENCODING_CC => FormulaType::Cc,
            ENCODING_PBC => FormulaType::Pbc,
            _ => panic!("Unexpected formula encoding"),
        }
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Copy, Clone, Hash)]
pub struct FormulaEncoding {
    pub encoding: u64,
}

impl FormulaEncoding {
    pub const fn is_large(self) -> bool {
        is_64_index(self.encoding >> INDEX_ENCODING_SHIFT)
    }

    pub const fn as_32(self) -> SmallFormulaEncoding {
        truncate_64(self)
    }

    pub fn encode_type(ty: FormulaType) -> Self {
        Self::encode(0, ty, true)
    }
}

#[allow(clippy::cast_lossless)]
impl Encoding for FormulaEncoding {
    fn encode(index: u64, ty: FormulaType, large_cache: bool) -> Self {
        use FormulaType::{And, Cc, Equiv, False, Impl, Lit, Not, Or, Pbc, True};
        let encoding = match ty {
            True => header(ENCODING_TRUE, large_cache) as u64,
            False => header(ENCODING_FALSE, large_cache) as u64,
            And => header(ENCODING_AND, large_cache) as u64 | index_64(index),
            Or => header(ENCODING_OR, large_cache) as u64 | index_64(index),
            Not => header(ENCODING_NOT, large_cache) as u64 | index_64(index),
            Impl => header(ENCODING_IMPL, large_cache) as u64 | index_64(index),
            Equiv => header(ENCODING_EQUIV, large_cache) as u64 | index_64(index),
            Cc => header(ENCODING_CC, large_cache) as u64 | index_64(index),
            Pbc => header(ENCODING_PBC, large_cache) as u64 | index_64(index),
            Lit(LitType::Pos(VarType::FF)) => header(ENCODING_POS_FF, large_cache) as u64 | index_64(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::CNF))) => header(ENCODING_POS_AUX_CNF, large_cache) as u64 | index_64(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::CC))) => header(ENCODING_POS_AUX_CC, large_cache) as u64 | index_64(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::PB))) => header(ENCODING_POS_AUX_PB, large_cache) as u64 | index_64(index),
            Lit(LitType::Neg(VarType::FF)) => header(ENCODING_NEG_FF, large_cache) as u64 | index_64(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::CNF))) => header(ENCODING_NEG_AUX_CNF, large_cache) as u64 | index_64(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::CC))) => header(ENCODING_NEG_AUX_CC, large_cache) as u64 | index_64(index),
            Lit(LitType::Neg(VarType::Aux(AuxVarType::PB))) => header(ENCODING_NEG_AUX_PB, large_cache) as u64 | index_64(index),
            Lit(LitType::Pos(VarType::Aux(AuxVarType::TMP)) | LitType::Neg(VarType::Aux(AuxVarType::TMP))) => {
                panic!("Solver variables or temporary aux variables should not be encoded!")
            }
        };
        Self { encoding }
    }

    fn to_formula(self) -> EncodedFormula {
        EncodedFormula { encoding: self }
    }

    fn index(self) -> u64 {
        self.encoding >> INDEX_ENCODING_SHIFT
    }

    #[allow(clippy::cast_possible_truncation)]
    fn is_large_cache(self) -> bool {
        (self.encoding as u8) & CACHE_ENCODE_MASK != 0
    }

    #[allow(clippy::cast_possible_truncation)]
    fn formula_type(self) -> FormulaType {
        match (self.encoding as u8) & TYPE_ENCODE_MASK {
            ENCODING_TRUE => FormulaType::True,
            ENCODING_FALSE => FormulaType::False,
            ENCODING_POS_FF => FormulaType::Lit(LitType::Pos(VarType::FF)),
            ENCODING_POS_AUX_CNF => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::CNF))),
            ENCODING_POS_AUX_CC => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::CC))),
            ENCODING_POS_AUX_PB => FormulaType::Lit(LitType::Pos(VarType::Aux(AuxVarType::PB))),
            ENCODING_NEG_FF => FormulaType::Lit(LitType::Neg(VarType::FF)),
            ENCODING_NEG_AUX_CNF => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::CNF))),
            ENCODING_NEG_AUX_CC => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::CC))),
            ENCODING_NEG_AUX_PB => FormulaType::Lit(LitType::Neg(VarType::Aux(AuxVarType::PB))),
            ENCODING_AND => FormulaType::And,
            ENCODING_OR => FormulaType::Or,
            ENCODING_NOT => FormulaType::Not,
            ENCODING_IMPL => FormulaType::Impl,
            ENCODING_EQUIV => FormulaType::Equiv,
            ENCODING_CC => FormulaType::Cc,
            ENCODING_PBC => FormulaType::Pbc,
            _ => panic!("Unexpected formula encoding"),
        }
    }
}

const fn is_64_index(index: u64) -> bool {
    index > LARGES_32_INDEX as u64
}

pub(super) const fn extend_32(encoding: SmallFormulaEncoding) -> FormulaEncoding {
    FormulaEncoding { encoding: encoding.encoding as u64 }
}

#[allow(clippy::cast_possible_truncation)]
pub(super) const fn truncate_64(encoding: FormulaEncoding) -> SmallFormulaEncoding {
    SmallFormulaEncoding { encoding: encoding.encoding as u32 }
}
