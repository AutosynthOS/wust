use std::mem;
fn main() {
    println!("Aarch64Instruction: {} bytes", mem::size_of::<autosynth_isa_aarch64::Aarch64Instruction>());
    println!("  AddImm: {}", mem::size_of::<autosynth_isa_aarch64::AddImm>());
    println!("  AddReg: {}", mem::size_of::<autosynth_isa_aarch64::AddReg>());
    println!("  BCond: {}", mem::size_of::<autosynth_isa_aarch64::BCond>());
    println!("  Bl: {}", mem::size_of::<autosynth_isa_aarch64::Bl>());
    println!("  LdrPost: {}", mem::size_of::<autosynth_isa_aarch64::LdrPost>());
    println!("  LdrUoff: {}", mem::size_of::<autosynth_isa_aarch64::LdrUoff>());
    println!("  Movz: {}", mem::size_of::<autosynth_isa_aarch64::Movz>());
    println!("  OrrReg: {}", mem::size_of::<autosynth_isa_aarch64::OrrReg>());
    println!("  Ret: {}", mem::size_of::<autosynth_isa_aarch64::Ret>());
    println!("  StrPre: {}", mem::size_of::<autosynth_isa_aarch64::StrPre>());
    println!("  StrUoff: {}", mem::size_of::<autosynth_isa_aarch64::StrUoff>());
    println!("  SubImm: {}", mem::size_of::<autosynth_isa_aarch64::SubImm>());
    println!("  SubReg: {}", mem::size_of::<autosynth_isa_aarch64::SubReg>());
    println!("  SubsImm: {}", mem::size_of::<autosynth_isa_aarch64::SubsImm>());
    println!("  SubsReg: {}", mem::size_of::<autosynth_isa_aarch64::SubsReg>());
}
