use std::collections::HashMap;

#[derive(Debug, Default, PartialEq, Eq)]
pub struct CategoriesTable {
    categories: HashMap<CategoryId, CategoryData>,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct CategoryId(u64);

#[derive(Debug, PartialEq, Eq)]
pub struct CategoryData {
    /// A short description of the category, e.g. "work"
    pub summary: String,
}
