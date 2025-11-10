mod cc_config;
mod cc_encoder;
mod cc_incremental_data;

mod cc_amo_bimander;
mod cc_amo_binary;
mod cc_amo_commander;
mod cc_amo_ladder;
mod cc_amo_nested;
mod cc_amo_product;
mod cc_amo_pure;

pub(crate) mod cc_cardinality_networks;
pub(crate) mod cc_modular_totalizer;
pub(crate) mod cc_sorter;
pub(crate) mod cc_totalizer;

pub use cc_config::*;
pub use cc_encoder::*;
pub use cc_incremental_data::*;

use cc_amo_bimander::build_amo_bimander;
use cc_amo_binary::build_amo_binary;
use cc_amo_commander::build_amo_commander;
use cc_amo_ladder::build_amo_ladder;
use cc_amo_nested::build_amo_nested;
use cc_amo_product::build_amo_product;
use cc_amo_pure::build_amo_pure;

/// We deviate from the convention of putting unit tests in the source file in this case,
/// s.t. the files don't become too large
#[cfg(test)]
mod tests;
