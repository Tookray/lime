use crate::chip8::Chip8;
use crate::platform::Platform;

mod chip8;
mod platform;

fn main() {
    let space_invaders_rom = include_bytes!("../roms/Space Invaders [David Winter].ch8");

    let mut chip8 = Chip8::new();
    chip8
        .load_rom(space_invaders_rom)
        .expect("Failed to load ROM");

    let mut platform = Platform::new(chip8);

    platform.run();
}
