use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

const MEMORY_SIZE: u16 = 0x1000;
const SPRITE_START: u16 = 0x50;
const ROM_START: u16 = 0x200;

const SPRITES: [u8; 80] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, // 0
    0x20, 0x60, 0x20, 0x20, 0x70, // 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0, // 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0, // 3
    0x90, 0x90, 0xF0, 0x10, 0x10, // 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0, // 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0, // 6
    0xF0, 0x10, 0x20, 0x40, 0x40, // 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0, // 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0, // 9
    0xF0, 0x90, 0xF0, 0x90, 0x90, // A
    0xE0, 0x90, 0xE0, 0x90, 0xE0, // B
    0xF0, 0x80, 0x80, 0x80, 0xF0, // C
    0xE0, 0x90, 0x90, 0x90, 0xE0, // D
    0xF0, 0x80, 0xF0, 0x80, 0xF0, // E
    0xF0, 0x80, 0xF0, 0x80, 0x80, // F
];

pub const DISPLAY_WIDTH: usize = 64;
pub const DISPLAY_HEIGHT: usize = 32;

/// Extracts `_nnn` from an opcode.
macro_rules! nnn {
    ($opcode:expr) => {
        $opcode & 0x0FFF
    };
}

/// Extracts `___n` from an opcode.
macro_rules! n {
    ($opcode:expr) => {
        $opcode & 0x000F
    };
}

/// Extracts `_x__` from an opcode. Since `x` is used to index registers, it is
/// returned as a `usize`.
macro_rules! x {
    ($opcode:expr) => {
        (($opcode & 0x0F00) >> 8) as usize
    };
}

/// Extracts `__y_` from an opcode. Since `y` is used to index registers, it is
/// returned as a `usize`.
macro_rules! y {
    ($opcode:expr) => {
        (($opcode & 0x00F0) >> 4) as usize
    };
}

/// Extracts `__kk` from an opcode. Since `kk` is used to compare values against
/// registers, it is returned as a `u8`.
macro_rules! kk {
    ($opcode:expr) => {
        ($opcode & 0x00FF) as u8
    };
}

pub struct Chip8<R: Rng> {
    stack_pointer: usize,
    stack: [u16; 0x10],

    memory: [u8; MEMORY_SIZE as usize],

    registers: [u8; 0x10],
    index: u16,
    program_counter: u16,
    delay_timer: u8,
    sound_timer: u8,

    op_code: u16,

    // The platform will set the keypad values. I don't think it's worth the
    // hassle to provide a method to set the keypad values.
    pub keypad: [u8; 0x10],

    // The platform will draw the display, so we will also need to expose it as
    // well.
    pub display: [u8; DISPLAY_WIDTH * DISPLAY_HEIGHT],

    // There is an instruction that places a random number in a register. So, we
    // need a random number generator.
    rng: R,
}

impl Chip8<SmallRng> {
    pub fn new() -> Self {
        let mut memory = [0; MEMORY_SIZE as usize];

        // Load the sprites (fonts) into memory.
        for (i, &byte) in SPRITES.iter().enumerate() {
            memory[i] = byte;
        }

        Self {
            stack_pointer: 0,
            stack: [0; 0x10],

            memory,

            registers: [0; 0x10],
            index: 0,
            program_counter: ROM_START as u16,
            delay_timer: 0,
            sound_timer: 0,

            op_code: 0,

            keypad: [0; 0x10],
            display: [0; DISPLAY_WIDTH * DISPLAY_HEIGHT],

            // NOTE: Could pass a random seed to the constructor when we
            // initialize the emulator.
            rng: SmallRng::from_entropy(),
        }
    }

    pub fn load_rom(&mut self, rom: &[u8]) -> Result<(), Error> {
        // Make sure the ROM fits in memory
        if rom.len() >= self.memory.len() - (ROM_START as usize) {
            return Err(Error::RomTooLarge);
        }

        for (i, &byte) in rom.iter().enumerate() {
            self.memory[(ROM_START as usize) + i] = byte;
        }

        Ok(())
    }

    // TODO: Decouple the timers from the CPU cycle.
    // Since this method decrements the delay and sound timer, it expects to be
    // called at a regular interval of 60Hz.
    pub fn cycle(&mut self) {
        // Fetch the opcode.
        self.op_code = (self.memory[self.program_counter as usize] as u16) << 8
            | self.memory[(self.program_counter + 1) as usize] as u16;

        // Increment the program counter by 2 to get to the next opcode.
        self.program_counter += 2;

        // Decode and execute the opcode.
        self.execute();

        // Decrement the delay timer if it's been set.
        if self.delay_timer > 0 {
            self.delay_timer -= 1;
        }

        // Decrement the sound timer if it's been set.
        if self.sound_timer > 0 {
            self.sound_timer -= 1;
        }
    }

    fn execute(&mut self) {
        // The easiest way to decode an opcode it with a match statement, but it
        // gets messy when you have a lot of instructions.
        //
        // We could implement an array of function pointers where the opcode is
        // an index into an array of function pointers. The downside is that we
        // must have an array big enough to account for every opcode because the
        // opcode is an index into the array. Dereferencing a pointer for every
        // instruction may also have problems, but when your emulator is complex
        // it's probably worth it.
        match self.op_code {
            0x00E0 => self.op_00e0(),
            0x00EE => self.op_00ee(),
            0x1000..=0x1FFF => self.op_1nnn(),
            0x2000..=0x2FFF => self.op_2nnn(),
            0x3000..=0x3FFF => self.op_3xkk(),
            0x4000..=0x4FFF => self.op_4xkk(),
            0x5000..=0x5FFF => self.op_5xy0(),
            0x6000..=0x6FFF => self.op_6xkk(),
            0x7000..=0x7FFF => self.op_7xkk(),
            0x8000..=0x8FFF => match self.op_code & 0x000F {
                0x0 => self.op_8xy0(),
                0x1 => self.op_8xy1(),
                0x2 => self.op_8xy2(),
                0x3 => self.op_8xy3(),
                0x4 => self.op_8xy4(),
                0x5 => self.op_8xy5(),
                0x6 => self.op_8xy6(),
                0x7 => self.op_8xy7(),
                0xE => self.op_8xye(),
                _ => unreachable!("Unknown opcode: {:#X}", self.op_code),
            },
            0x9000..=0x9FFF => self.op_9xy0(),
            0xA000..=0xAFFF => self.op_annn(),
            0xB000..=0xBFFF => self.op_bnnn(),
            0xC000..=0xCFFF => self.op_cxkk(),
            0xD000..=0xDFFF => self.op_dxyn(),
            0xE000..=0xEFFF => match self.op_code & 0x00FF {
                0x9E => self.op_ex9e(),
                0xA1 => self.op_exa1(),
                _ => unreachable!("Unknown opcode: {:#X}", self.op_code),
            },
            0xF000..=0xFFFF => match self.op_code & 0x00FF {
                0x07 => self.op_fx07(),
                0x0A => self.op_fx0a(),
                0x15 => self.op_fx15(),
                0x18 => self.op_fx18(),
                0x1E => self.op_fx1e(),
                0x29 => self.op_fx29(),
                0x33 => self.op_fx33(),
                0x55 => self.op_fx55(),
                0x65 => self.op_fx65(),
                _ => unreachable!("Unknown opcode: {:#X}", self.op_code),
            },
            _ => unreachable!("Unknown opcode: {:#X}", self.op_code),
        }
    }

    /// Returns a random number between 0 and 255.
    fn random_byte(&mut self) -> u8 {
        self.rng.gen()
    }
}

/// The Chip-8 has 34 instructions that we need to emulate.
///
/// Note that there are differing opinions on about how certain instructions
/// should behave. I'll be following Cowgod's Chip-8 technical reference.
impl Chip8<SmallRng> {
    /// `CLS`: opcode `00E0`
    ///
    /// Clear the display.
    fn op_00e0(&mut self) {
        // We can simply set the entire display to zeroes.

        // Consider using this instead if performance is an issue.
        //
        // use std::ptr;
        //
        // unsafe {
        //     ptr::write_bytes(self.display.as_mut_ptr(), 0, self.display.len());
        // }

        // Simply set the entire video buffer to 0.
        for pixel in self.display.iter_mut() {
            *pixel = 0;
        }
    }

    /// `RET`: opcode `00EE`
    ///
    /// Return from a subroutine.
    fn op_00ee(&mut self) {
        // The top of the stack has the address of one instruction past the one
        // that called the subroutine, so we can put that back into the program
        // counter. Note that this overwrites our preemtive `pc += 2` earlier.

        self.stack_pointer -= 1;
        self.program_counter = self.stack[self.stack_pointer];
    }

    /// `JP addr`: opcode `1nnn`
    ///
    /// Jump to location `nnn`.
    ///
    /// The interpreter sets the program counter to `nnn`.
    fn op_1nnn(&mut self) {
        // A jump doesn't remember its origin, so no stack interaction is
        // required.

        self.program_counter = nnn!(self.op_code);
    }

    /// `CALL addr`: opcode `2nnn`
    ///
    /// Call subroutine at `nnn`.
    fn op_2nnn(&mut self) {
        // When we call a subroutine, we want to return eventually. So, we put
        // the current program counter onto the top of the stack. Remember that
        // we did `pc += 2` in `Cycle()` so the current program counter holds
        // the next instruction after this `CALL`, which is correct. We don't
        // want to return to the `CALL` instruction because it would be an
        // infinite loop of `CALL`s and `RET`s.

        self.stack[self.stack_pointer] = self.program_counter;
        self.stack_pointer += 1;

        self.program_counter = nnn!(self.op_code);
    }

    /// `SE Vx, byte`: opcode `3xkk`
    ///
    /// Skip next instruction if `Vx = kk`.
    fn op_3xkk(&mut self) {
        // Since our program counter has already been incremented by 2 in
        // `Cycle()`, we can just increment by 2 again to skip the next
        // instruction.

        let x = x!(self.op_code);
        let kk = kk!(self.op_code);

        if self.registers[x] == kk {
            self.program_counter += 2;
        }
    }

    /// `SNE Vx, byte`: opcode `4xkk`
    ///
    /// Skip next instruction if `Vx != kk`.
    fn op_4xkk(&mut self) {
        // Since our program counter has already been incremented by 2 in
        // `Cycle()`, we can just increment by 2 again to skip the next
        // instruction.

        let x = x!(self.op_code);
        let kk = kk!(self.op_code);

        if self.registers[x] != kk {
            self.program_counter += 2;
        }
    }

    /// `SE Vx, Vy`: opcode `5xy0`
    ///
    /// Skip next instruction if `Vx = Vy`.
    fn op_5xy0(&mut self) {
        // Since our program counter has already been incremented by 2 in
        // `Cycle()`, we can just increment by 2 again to skip the next
        // instruction.

        let x = x!(self.op_code);
        let y = y!(self.op_code);

        if self.registers[x] == self.registers[y] {
            self.program_counter += 2;
        }
    }

    /// `LD Vx, byte`: opcode `6xkk`
    ///
    /// Set `Vx = kk`.
    fn op_6xkk(&mut self) {
        let x = x!(self.op_code);
        let kk = kk!(self.op_code);

        self.registers[x] = kk;
    }

    /// `ADD Vx, byte`: opcode `7xkk`
    ///
    /// Set `Vx = Vx + kk`.
    fn op_7xkk(&mut self) {
        let x = x!(self.op_code);
        let kk = kk!(self.op_code);

        // Allow overflow.
        self.registers[x] = self.registers[x].wrapping_add(kk);
    }

    /// `LD Vx, Vy`: opcode `8xy0`
    ///
    /// Set `Vx = Vy`.
    fn op_8xy0(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        self.registers[x] = self.registers[y];
    }

    /// `OR Vx, Vy`: opcode `8xy1`
    ///
    /// Set `Vx = Vx OR Vy`.
    fn op_8xy1(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        self.registers[x] |= self.registers[y];
    }

    /// `AND Vx, Vy`: opcode `8xy2`
    ///
    /// Set Vx = Vx AND Vy.
    fn op_8xy2(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        self.registers[x] &= self.registers[y];
    }

    /// `XOR Vx, Vy`: opcode `8xy3`
    ///
    /// Set Vx = Vx XOR Vy.
    fn op_8xy3(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        self.registers[x] ^= self.registers[y];
    }

    /// `ADD Vx, Vy`: opcode `8xy4`
    ///
    /// Set `Vx = Vx + Vy`, set `VF = carry`.
    ///
    /// The values of `Vx` and `Vy` are added together. If the result is greater
    /// than 8 bits (255) `VF` is set to 1, otherwise 0. Only the lowest 8 bits
    /// of the result are kept, and stored in `Vx`.
    fn op_8xy4(&mut self) {
        // This is an `ADD` with an overflow flag. If the sum is greater than
        // what can fit into a byte (255), register `VF` will be set to 1 as a
        // flag.

        let x = x!(self.op_code);
        let y = y!(self.op_code);

        let (result, overflow) = self.registers[x].overflowing_add(self.registers[y]);

        self.registers[x] = result;
        self.registers[0xF] = if overflow { 1 } else { 0 };
    }

    /// `SUB Vx, Vy`: opcode `8xy5`
    ///
    /// Set `Vx = Vx - Vy`, set `VF = NOT borrow`.
    ///
    /// If `Vx > Vy`, then `VF` is set to 1, otherwise 0. Then `Vy` is
    /// subtracted from `Vx`, and the results stored in `Vx`.
    fn op_8xy5(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        let (result, overflow) = self.registers[x].overflowing_sub(self.registers[y]);

        self.registers[x] = result;

        self.registers[0xF] = if !overflow { 1 } else { 0 };
    }

    /// `SHR Vx {, Vy}`: opcode `8xy6`
    ///
    /// Set `Vx = Vx SHR 1`.
    ///
    /// If the least-significant bit of `Vx` is 1, then `VF` is set to 1,
    /// otherwise 0. Then `Vx` is divided by 2.
    fn op_8xy6(&mut self) {
        // A right shift is performed (division by 2), and the least significant
        // bit is saved in register `VF`.

        // Why is there a `y` in the operation code? It's not used.
        let x = x!(self.op_code);

        self.registers[0xF] = self.registers[x] & 0x1;
        self.registers[x] >>= 1;
    }

    /// `SUBN Vx, Vy`: opcode `8xy7`
    ///
    /// Set `Vx = Vy - Vx`, set `VF = NOT borrow`.
    ///
    /// If `Vy > Vx`, then `VF` is set to 1, otherwise 0. Then `Vx` is
    /// subtracted from `Vy`, and the results stored in `Vx`.
    fn op_8xy7(&mut self) {
        let x = x!(self.op_code);
        let y = y!(self.op_code);

        let (result, overflow) = self.registers[y].overflowing_sub(self.registers[x]);

        self.registers[x] = result;
        self.registers[0xF] = if !overflow { 1 } else { 0 };
    }

    /// `SHL Vx {, Vy}`: opcode `8xye`
    ///
    /// Set `Vx = Vx SHL 1`.
    ///
    /// If the most-significant bit of `Vx` is 1, then `VF` is set to 1,
    /// otherwise to 0. Then `Vx` is multiplied by 2.
    fn op_8xye(&mut self) {
        let x = x!(self.op_code);

        self.registers[0xF] = (self.registers[x] & 0b1000_0000) >> 7;
        self.registers[x] <<= 1;
    }

    /// `SNE Vx, Vy`: opcode `9xy0`
    ///
    /// Skip next instruction if `Vx != Vy`.
    fn op_9xy0(&mut self) {
        // Since our program counter has already been incremented by 2 in
        // `Cycle()`, we can just increment by 2 again to skip the next
        // instruction.

        let x = x!(self.op_code);
        let y = y!(self.op_code);

        if self.registers[x] != self.registers[y] {
            self.program_counter += 2;
        }
    }

    /// `LD I, addr`: opcode `Annn`
    ///
    /// Set `I = nnn`.
    fn op_annn(&mut self) {
        let nnn = nnn!(self.op_code);

        self.index = nnn;
    }

    /// `JP V0, addr`: opcode `Bnnn`
    ///
    /// Jump to location `nnn + V0`.
    fn op_bnnn(&mut self) {
        let nnn = nnn!(self.op_code);

        self.program_counter = nnn + (self.registers[0] as u16);
    }

    /// `RND Vx, byte`: opcode `Cxkk`
    ///
    /// Set `Vx = random byte AND kk`.
    fn op_cxkk(&mut self) {
        let x = x!(self.op_code);
        let kk = kk!(self.op_code);

        self.registers[x] = self.random_byte() & kk;
    }

    /// `DRW Vx, Vy, nibble`: opcode `Dxyn`
    ///
    /// Display n-byte sprite starting at memory location `I` at `(Vx, Vy)`, set
    /// `VF = collision`.
    fn op_dxyn(&mut self) {
        // We iterate over the sprite, row by row and column by column. We know
        // there are eight columns because a sprite is guaranteed to be eight
        // pixels wide.
        //
        // If a sprite pixel is on then there may be a collision with what's
        // already being displayed, so we check if our screen pixel in the same
        // location is set. If so we must set the `VF` register to express
        // collision.
        //
        // Then we can just `XOR` the sprite pixel with `0xFF` to essentially
        // `XOR` it with the sprite pixel (which we now know is on). We can't
        // `XOR` directly because the sprite pixel is either 1 or 0 while our
        // video pixel is either `0x00` or `0XFF`.

        let x = x!(self.op_code);
        let y = y!(self.op_code);
        let n = n!(self.op_code);

        // Wrap if going beyond the screen boundaries.
        let x = (self.registers[x] as usize) % DISPLAY_WIDTH;
        let y = (self.registers[y] as usize) % DISPLAY_HEIGHT;

        self.registers[0xF] = 0;

        for row in 0..n {
            let sprite_byte = self.memory[(self.index + row) as usize];

            for col in 0..8 {
                let sprite_pixel = sprite_byte & (0b1000_0000 >> col);
                let screen_pixel = self.display[(y + row as usize) * DISPLAY_WIDTH + (x + col)];

                // The sprite pixel is on.
                if sprite_pixel != 0 {
                    // The screen pixel is also on. There is a collision.
                    if screen_pixel != 0 {
                        self.registers[0xF] = 1;
                    }

                    // `XOR` the sprite pixel with the screen pixel.
                    self.display[(y + row as usize) * DISPLAY_WIDTH + (x + col)] ^= 0xFF;
                }
            }
        }
    }

    /// `SKP Vx`: opcode `Ex9e`
    ///
    /// Skip next instruction if key with the value of `Vx` is pressed.
    fn op_ex9e(&mut self) {
        // Since our program counter has already been incremented by 2 in
        // `Cycle()`, we can just increment by 2 again to skip the next
        // instruction.
        let x = x!(self.op_code);
        let key = self.registers[x] as usize;

        if self.keypad[key] != 0 {
            self.program_counter += 2;
        }
    }

    /// `SKNP Vx`: opcode `Exa1`
    ///
    /// Skip next instruction if key with the value of `Vx` is not pressed.
    fn op_exa1(&mut self) {
        let x = x!(self.op_code);
        let key = self.registers[x] as usize;

        if self.keypad[key] == 0 {
            self.program_counter += 2;
        }
    }

    /// `LD Vx, DT`: opcode `Fx07`
    ///
    /// Set `Vx = delay timer value`.
    fn op_fx07(&mut self) {
        let x = x!(self.op_code);

        self.registers[x] = self.delay_timer;
    }

    /// `LD Vx, K`: opcode `Fx0a`
    ///
    /// Wait for a key press, store the value of the key in `Vx`.
    fn op_fx0a(&mut self) {
        // The easiest way to "wait" is to decrement the program counter by 2
        // whenever a keypad value is not detected. This has the effect of
        // running the same instruction repeatedly.
        let x = x!(self.op_code);

        for i in 0..16 {
            if self.keypad[i] != 0 {
                self.registers[x] = i as u8;

                return;
            }
        }

        self.program_counter -= 2;
    }

    /// `LD DT, Vx`: opcode `Fx15`
    ///
    /// Set `delay timer = Vx`.
    fn op_fx15(&mut self) {
        let x = x!(self.op_code);

        self.delay_timer = self.registers[x];
    }

    /// `LD ST, Vx`: opcode `Fx18`
    ///
    /// Set `sound timer = Vx`.
    fn op_fx18(&mut self) {
        let x = x!(self.op_code);

        self.sound_timer = self.registers[x];
    }

    /// `ADD I, Vx`: opcode `Fx1e`
    ///
    /// Set `I = I + Vx`.
    fn op_fx1e(&mut self) {
        let x = x!(self.op_code);

        self.index += self.registers[x] as u16;
    }

    /// `LD F, Vx`: opcode `Fx29`
    ///
    /// Set `I = location of sprite for digit Vx`.
    fn op_fx29(&mut self) {
        // We know the font characters are located at `0x50`, and we know
        // they're 5 bytes each, so we can get the address of the first byte of
        // any character by taking an offset from the start address.
        let x = x!(self.op_code);

        let digit = self.registers[x] as u16;

        self.index = SPRITE_START + (5 * digit);
    }

    /// `LD B, Vx`: opcode `Fx33`
    ///
    /// Store BCD representation of `Vx` in memory locations `I`, `I+1`, and
    /// `I+2`.
    ///
    /// The interpreter takes the decimal value of `Vx`, and places the hundreds
    /// digit in memory at location in `I`, the tens digit at location `I+1`,
    /// and the ones digit at location `I+2`.
    fn op_fx33(&mut self) {
        // We can use the modulus operator to get the right-most digit of a
        // number, and then do a division to remove that digit. A division by
        // ten will either completely remove the digit (`340 / 10 = 34`), or
        // result in a float which will be truncated (`345 / 10 = 34.5 = 34`).
        let x = x!(self.op_code);

        let mut value = self.registers[x];

        // Ones
        self.memory[(self.index + 2) as usize] = value % 10;
        value /= 10;

        // Tens
        self.memory[(self.index + 1) as usize] = value % 10;
        value /= 10;

        // Hundreds
        self.memory[self.index as usize] = value % 10;
    }

    /// `LD [I], Vx`: opcode `Fx55`
    ///
    /// Store registers `V0` through `Vx` in memory starting at location `I`.
    fn op_fx55(&mut self) {
        let x = x!(self.op_code);

        for i in 0..=x {
            self.memory[(self.index + (i as u16)) as usize] = self.registers[i];
        }
    }

    /// `LD Vx, [I]`: opcode `Fx65`
    ///
    /// Read registers `V0` through `Vx` from memory starting at location `I`.
    fn op_fx65(&mut self) {
        let x = x!(self.op_code);

        for i in 0..=x {
            self.registers[i] = self.memory[(self.index + i as u16) as usize];
        }
    }
}

#[derive(Debug)]
pub enum Error {
    RomTooLarge,
}
