const std = @import("std");
pub const compress = @import("compress.zig");
pub const decompress = std.compress.zstd.decompress;

comptime {
    std.testing.refAllDecls(compress);
}
