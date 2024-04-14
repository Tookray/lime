use std::time::{Duration, Instant};

use rand::rngs::SmallRng;
use rand::Rng;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::VideoSubsystem;

use crate::chip8::{self, Chip8};

const SCALE: i32 = 10;

// I really don't like that `R` from the `Chip8` struct is being leaked into the
// `Platform` struct. I'm not sure how to fix this yet unless I specify the
// `chip8` member as `Chip8<SmallRng>`.
pub struct Platform<R: Rng> {
    video: VideoSubsystem,

    chip8: Chip8<R>,
}

impl Platform<SmallRng> {
    pub fn new(chip8: Chip8<SmallRng>) -> Self {
        let context = sdl2::init().expect("Failed to initialize SDL2");
        let video = context
            .video()
            .expect("Failed to initialize video subsystem");

        Self { video, chip8 }
    }

    pub fn run(&mut self) {
        let window = self
            .video
            .window(
                "Chip-8 Emulator",
                // Scale the window size since the original resolution is small.
                chip8::DISPLAY_WIDTH as u32 * SCALE as u32,
                chip8::DISPLAY_HEIGHT as u32 * SCALE as u32,
            )
            .position_centered()
            .build()
            .expect("Failed to create window");

        let mut canvas = window
            .into_canvas()
            .build()
            .expect("Failed to create canvas");

        // An event pump is used to handle input events.
        let mut event_pump = self
            .video
            .sdl()
            .event_pump()
            .expect("Failed to get event pump");

        let mut timestamp = Instant::now();

        'running: loop {
            for event in event_pump.poll_iter() {
                if !self.process_input(event) {
                    break 'running;
                }
            }

            // Instead of sleeping the thread for a fixed amount of time, I
            // think we should just loop until the next frame is ready.
            let time_elapsed = timestamp.elapsed();

            if time_elapsed >= Duration::from_millis(2) {
                // Run the emulator for a single cycle.
                self.chip8.cycle();

                // Update the display.
                for (i, pixel) in self.chip8.display.iter().enumerate() {
                    let x = (i % chip8::DISPLAY_WIDTH) as i32;
                    let y = (i / chip8::DISPLAY_WIDTH) as i32;

                    let colour = if *pixel == 0 {
                        Color::RGB(0, 0, 0)
                    } else {
                        Color::RGB(255, 255, 255)
                    };

                    canvas.set_draw_color(colour);

                    // We are drawing a rectangle for each pixel. This probably
                    // isn't the most optimal way to do it, but I don't know
                    // enough about SDL2 to do it better for now.
                    canvas
                        .fill_rect(sdl2::rect::Rect::new(
                            x * SCALE,
                            y * SCALE,
                            SCALE as u32,
                            SCALE as u32,
                        ))
                        .unwrap();
                }

                canvas.present();

                // Reset the timer.
                timestamp = Instant::now();
            }
        }
    }

    /// Returns `false` if the application should exit.
    fn process_input(&mut self, event: Event) -> bool {
        match event {
            Event::Quit { .. } => return false,
            Event::KeyDown {
                keycode: Some(keycode),
                ..
            } => {
                if let Some(key) = self.keypad(keycode) {
                    *key = 1;
                }
            }
            Event::KeyUp {
                keycode: Some(keycode),
                ..
            } => {
                if let Some(key) = self.keypad(keycode) {
                    *key = 0;
                }
            }

            // Ignore all other events.
            _ => {}
        };

        true
    }

    /// Returns a reference to the keypad element at the given index.
    fn keypad(&mut self, keycode: Keycode) -> Option<&mut u8> {
        // Keypad layout:
        // 1 2 3 4 -> 1 2 3 C
        // Q W E R -> 4 5 6 D
        // A S D F -> 7 8 9 E
        // Z X C V -> A 0 B F
        match keycode {
            Keycode::Num1 => Some(&mut self.chip8.keypad[0x1]),
            Keycode::Num2 => Some(&mut self.chip8.keypad[0x2]),
            Keycode::Num3 => Some(&mut self.chip8.keypad[0x3]),
            Keycode::Num4 => Some(&mut self.chip8.keypad[0xC]),
            Keycode::Q => Some(&mut self.chip8.keypad[0x4]),
            Keycode::W => Some(&mut self.chip8.keypad[0x5]),
            Keycode::E => Some(&mut self.chip8.keypad[0x6]),
            Keycode::R => Some(&mut self.chip8.keypad[0xD]),
            Keycode::A => Some(&mut self.chip8.keypad[0x7]),
            Keycode::S => Some(&mut self.chip8.keypad[0x8]),
            Keycode::D => Some(&mut self.chip8.keypad[0x9]),
            Keycode::F => Some(&mut self.chip8.keypad[0xE]),
            Keycode::Z => Some(&mut self.chip8.keypad[0xA]),
            Keycode::X => Some(&mut self.chip8.keypad[0x0]),
            Keycode::C => Some(&mut self.chip8.keypad[0xB]),
            Keycode::V => Some(&mut self.chip8.keypad[0xF]),
            _ => None,
        }
    }
}

#[derive(Debug)]
enum Error {
    Sdl2,
}
