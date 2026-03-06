pub struct Signature {
    call_conv: CallConv,
    pub params: Vec<AbiParam>,
    pub returns: Vec<AbiParam>,
}

pub enum CallConv {
    WasmABI,
}

pub enum AbiParam {
    I32,
    I64,
    F32,
    F64,
    V128,
}

impl Signature {
    pub fn new(call_conv: CallConv) -> Self {
        Self {
            call_conv,
            params: Vec::new(),
            returns: Vec::new(),
        }
    }
}
