//! Parsed component type definitions (immutable "code" side).
//!
//! These types represent the structure of a component as parsed from its
//! binary format. They are analogous to `Module` for core wasm — immutable
//! data that describes what the component contains.

use std::collections::HashMap;

use crate::runtime::Value;

// ---------------------------------------------------------------------------
// Core instance definitions
// ---------------------------------------------------------------------------

/// How a core instance is created within a component.
#[derive(Clone)]
pub(crate) enum CoreInstanceDef {
    /// Instantiate a core module, optionally with import args.
    Instantiate {
        module_index: u32,
        /// Each arg maps a module import namespace to a core instance index.
        args: Vec<(String, CoreInstanceArg)>,
    },
    /// Build a synthetic instance from explicit exports.
    FromExports(Vec<CoreInstanceExportDef>),
}

/// An arg to a core module instantiation — currently always an instance.
#[derive(Clone)]
pub(crate) enum CoreInstanceArg {
    Instance(u32),
}

/// An export in a `FromExports` instance definition.
///
/// Each entry says "export `name` as the core item of `kind` at `index`
/// in the component's core index space for that kind."
#[derive(Clone)]
pub(crate) struct CoreInstanceExportDef {
    pub name: String,
    pub kind: wasmparser::ExternalKind,
    pub index: u32,
}

// ---------------------------------------------------------------------------
// Core alias and func definitions
// ---------------------------------------------------------------------------

/// A core alias that references a core instance export by instance index
/// and export name.
///
/// Used for globals, memories, tables, and tags — all of which are always
/// aliases of a core instance export. (Core funcs use `CoreFuncDef` instead,
/// since they have additional variants like `Lower` and `ResourceNew`.)
#[derive(Clone)]
pub(crate) struct CoreAliasDef {
    pub instance_index: u32,
    pub name: String,
}

/// String encoding used by `canon lower` / `canon lift`.
///
/// Determines alignment requirements for string pointers in the
/// canonical ABI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StringEncoding {
    /// UTF-8 encoding. String pointers have 1-byte alignment.
    Utf8,
    /// UTF-16 encoding. String pointers must be 2-byte aligned.
    Utf16,
    /// Latin-1 or UTF-16 encoding. String pointers must be 2-byte aligned.
    Latin1Utf16,
}

impl StringEncoding {
    /// Return the required byte alignment for a string pointer with this
    /// encoding.
    pub(crate) fn pointer_alignment(self) -> u32 {
        match self {
            StringEncoding::Utf8 => 1,
            StringEncoding::Utf16 | StringEncoding::Latin1Utf16 => 2,
        }
    }
}

/// How a core func is defined within a component.
///
/// Most core funcs are aliases of core instance exports, but canonical
/// operations (lower, resource ops) and async builtins also occupy slots
/// in the core func index space.
#[derive(Clone)]
pub(crate) enum CoreFuncDef {
    /// Alias of a core instance export (the common case).
    AliasInstanceExport { instance_index: u32, name: String },
    /// `canon lower` — lowers a component func to a core func.
    Lower {
        func_index: u32,
        /// String encoding specified on `canon lower` (e.g. utf8, utf16,
        /// latin1+utf16). Determines alignment requirements for string
        /// pointers in the fused adapter path.
        string_encoding: StringEncoding,
        /// Core memory index for the caller's memory, used for reading
        /// string/list data and validating bounds in the fused path.
        memory_index: Option<u32>,
    },
    /// `canon resource.new` — creates a new resource handle.
    ResourceNew { resource: u32 },
    /// `canon resource.rep` — gets the i32 representation of a resource.
    ResourceRep { resource: u32 },
    /// `canon resource.drop` — drops a resource handle.
    ResourceDrop { resource: u32 },
    /// Placeholder for async/thread builtins that we don't yet implement.
    AsyncBuiltin,
}

// ---------------------------------------------------------------------------
// Component-level value types
// ---------------------------------------------------------------------------

/// A lifted component-level value after canonical ABI processing.
///
/// Core wasm values (i32, i64, etc.) are lifted into their component-level
/// types (bool, char, string, etc.) based on the function's declared type.
#[derive(Debug, Clone)]
pub enum ComponentValue {
    Bool(bool),
    S8(i32),
    U8(u32),
    S16(i32),
    U16(u32),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    Char(char),
    String(String),
}

/// A component-level argument for canonical ABI lowering.
///
/// Wraps either a scalar value (lowered directly to a core `Value`) or a
/// list of component values (lowered via realloc + memory write to a
/// `(ptr, len)` pair of i32 core args).
#[derive(Debug, Clone)]
pub enum ComponentArg {
    /// A scalar value passed directly as a core wasm value.
    Value(Value),
    /// A list of component values, lowered via canonical ABI.
    // TODO: list lowering is incomplete — element_size is hardcoded to 1 and
    // no actual element data is written to memory. See `lower_list` in
    // canonical_abi.rs.
    List(Vec<ComponentArg>),
}

/// Simplified component value type for canonical ABI lifting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComponentResultType {
    Bool,
    S8,
    U8,
    S16,
    U16,
    S32,
    U32,
    S64,
    U64,
    F32,
    F64,
    Char,
    String,
    /// No result (unit function).
    Unit,
    /// A variant type with a known number of cases.
    Variant {
        case_count: u32,
    },
    /// A compound type (tuple, record, list) that uses retptr/argptr
    /// when passed across the ABI boundary. The alignment is the maximum
    /// alignment of the type's fields (e.g. 4 for tuples of u32).
    Compound {
        alignment: u32,
    },
    /// An owned resource handle — transferred across the ABI boundary.
    Own,
    /// A borrowed resource handle — the callee receives the rep value.
    Borrow,
    /// A type we don't yet handle — pass through raw.
    Unknown,
}

// ---------------------------------------------------------------------------
// Component function and export definitions
// ---------------------------------------------------------------------------

/// How a component-level function is defined within a component.
///
/// Most component funcs come from `canon lift`, but they can also be
/// aliased from a component instance export.
#[derive(Clone)]
pub(crate) enum ComponentFuncDef {
    /// Created by `canon lift` — a core func lifted to component level.
    Lift {
        core_func_index: u32,
        type_index: u32,
        /// Core memory index for canonical ABI operations (string lifting, etc.).
        memory_index: Option<u32>,
        /// Core func index of the realloc function for list/string lowering.
        realloc_func_index: Option<u32>,
    },
    /// Aliased from a component instance export.
    AliasInstanceExport { instance_index: u32, name: String },
}

/// How a component instance is created within a component.
#[derive(Clone)]
pub(crate) enum ComponentInstanceDef {
    /// Instantiate an inner component with args.
    Instantiate {
        component_index: u32,
        args: Vec<(String, ComponentInstanceArg)>,
    },
    /// Alias a component instance from another component instance's export.
    /// Fields unused at runtime — only occupies an index slot.
    AliasInstanceExport,
    /// Re-export of an existing component instance (from `export` section).
    /// Only occupies an index slot at runtime.
    Reexport,
    /// A synthetic component instance built from explicit exports.
    ///
    /// At the component level these typically export types and other
    /// component-level items. At runtime we create an instance that
    /// carries the exported items' bytes.
    FromExports(Vec<ComponentInstanceExport>),
}

/// An export entry in a `FromExports` component instance definition.
#[derive(Clone)]
pub(crate) struct ComponentInstanceExport {
    pub name: String,
    pub kind: ComponentExternalKind,
    pub index: u32,
}

/// An arg to a component instantiation.
#[derive(Clone)]
pub(crate) enum ComponentInstanceArg {
    Instance(u32),
    Module(u32),
    Component(u32),
    Func(u32),
    Type(()),
}

/// A component-level export.
#[derive(Clone)]
pub(crate) struct ComponentExportDef {
    pub name: String,
    pub kind: ComponentExternalKind,
    pub index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ComponentExternalKind {
    Func,
    Module,
    Component,
    Instance,
    Value,
    Type,
}

impl From<wasmparser::ComponentExternalKind> for ComponentExternalKind {
    fn from(kind: wasmparser::ComponentExternalKind) -> Self {
        match kind {
            wasmparser::ComponentExternalKind::Func => Self::Func,
            wasmparser::ComponentExternalKind::Module => Self::Module,
            wasmparser::ComponentExternalKind::Component => Self::Component,
            wasmparser::ComponentExternalKind::Instance => Self::Instance,
            wasmparser::ComponentExternalKind::Value => Self::Value,
            wasmparser::ComponentExternalKind::Type => Self::Type,
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level component
// ---------------------------------------------------------------------------

/// The kind of a component-level import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentImportKind {
    Instance,
    Func,
    Module,
    Type,
    Component,
    Value,
}

/// A parsed component-level import declaration.
#[derive(Clone)]
pub struct ComponentImportDef {
    pub name: String,
    pub kind: ComponentImportKind,
    /// For instance imports, the names of exports required by the instance
    /// type. Empty for non-instance imports.
    pub required_exports: Vec<String>,
}

/// A parsed component — immutable "code" side, analogous to `Module`.
#[derive(Clone)]
pub struct ParsedComponent {
    pub(crate) core_modules: Vec<Vec<u8>>,
    pub(crate) core_instances: Vec<CoreInstanceDef>,
    pub(crate) core_funcs: Vec<CoreFuncDef>,
    pub(crate) core_globals: Vec<CoreAliasDef>,
    pub(crate) core_memories: Vec<CoreAliasDef>,
    pub(crate) core_tables: Vec<CoreAliasDef>,
    pub(crate) core_tags: Vec<CoreAliasDef>,
    pub(crate) component_funcs: Vec<ComponentFuncDef>,
    pub(crate) exports: Vec<ComponentExportDef>,
    /// Number of component-level type entries (for index space tracking).
    pub(crate) component_type_count: u32,
    /// Raw bytes for inner component definitions.
    pub(crate) inner_components: Vec<Vec<u8>>,
    /// Component-level instance definitions.
    pub(crate) component_instances: Vec<ComponentInstanceDef>,
    /// Number of component-level imports that are instances.
    /// These occupy the first N component instance indices.
    pub(crate) instance_import_count: u32,
    /// Component-level import declarations.
    pub(crate) imports: Vec<ComponentImportDef>,
    /// Required export names for instance types, keyed by type index.
    /// Populated from `ComponentType::Instance` declarations in the type section.
    pub(crate) instance_type_exports: HashMap<u32, Vec<String>>,
}

impl ParsedComponent {
    /// The component's import declarations.
    pub(crate) fn imports(&self) -> &[ComponentImportDef] {
        &self.imports
    }

    /// Create an empty component with all fields default-initialized.
    pub(crate) fn empty() -> Self {
        ParsedComponent {
            core_modules: Vec::new(),
            core_instances: Vec::new(),
            core_funcs: Vec::new(),
            core_globals: Vec::new(),
            core_memories: Vec::new(),
            core_tables: Vec::new(),
            core_tags: Vec::new(),
            component_funcs: Vec::new(),
            exports: Vec::new(),
            component_type_count: 0,
            inner_components: Vec::new(),
            component_instances: Vec::new(),
            instance_import_count: 0,
            imports: Vec::new(),
            instance_type_exports: HashMap::new(),
        }
    }
}
