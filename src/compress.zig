//! Zig implementation of the Zstandard (zstd) compression library
//! Based on the C reference implementation

const std = @import("std");
const mem = std.mem;
const math = std.math;

/// Error codes
pub const Error = error{
    Generic,
    NoForwardProgress,
    FrameParameterUnsupported,
    FrameParameterWindowTooLarge,
    CompressionParameterUnsupported,
    InitMissing,
    MemoryAllocation,
    StageWrong,
    DstSizeTooSmall,
    SrcSizeWrong,
    CorruptionDetected,
    ChecksumWrong,
    LiteralHeaderWrong,
    DictionaryCorrupted,
    DictionaryWrong,
    DictionaryCreationFailed,
    MaxCode,
    OutOfMemory,
};

/// Version information
pub const ZSTD_VERSION_MAJOR = 1;
pub const ZSTD_VERSION_MINOR = 6;
pub const ZSTD_VERSION_RELEASE = 0;

/// Magic numbers
pub const ZSTD_MAGICNUMBER = 0xFD2FB528;
pub const ZSTD_MAGIC_DICTIONARY = 0xEC30A437;
pub const ZSTD_MAGIC_SKIPPABLE_START = 0x184D2A50;

/// Constants
pub const ZSTD_CONTENTSIZE_UNKNOWN = math.maxInt(u64);
pub const ZSTD_CONTENTSIZE_ERROR = math.maxInt(u64) - 1;

pub const ZSTD_MAX_INPUT_SIZE = if (@sizeOf(usize) == 8) 0xFF00FF00FF00FF00 else 0xFF00FF00;

/// Default compression level
pub const ZSTD_CLEVEL_DEFAULT = 3;

/// Block size limits
pub const ZSTD_BLOCKSIZELOG_MAX = 17;
pub const ZSTD_BLOCKSIZE_MAX = 1 << ZSTD_BLOCKSIZELOG_MAX;

/// Window log limits
pub const ZSTD_WINDOWLOG_ABSOLUTEMIN = 10;

/// Sequence constants
pub const ZSTD_REP_NUM = 3;
pub const MINMATCH = 3;
pub const MaxLL = 35;
pub const MaxML = 52;
pub const MaxOff = 31;

/// Hash constants
const HASH_READ_SIZE = 8;
const kSearchStrength = 8;

/// Hash primes
const prime3bytes = 506832829;
const prime4bytes = 2654435761;
const prime5bytes = 889523592379;
const prime6bytes = 227718039650203;
const prime7bytes = 58295818150454627;
const prime8bytes = 0xCF1BBCDCB7A56463;

/// Hash functions
fn ZSTD_hash3(u: u32, h: u32, s: u32) u32 {
    return (((u << (32 - 24)) *% prime3bytes) ^ s) >> (32 - h);
}

fn ZSTD_hash4(u: u32, h: u32, s: u32) u32 {
    if (h >= 32) return (u *% prime4bytes) ^ s;
    const shift = 32 - h;
    return ((u *% prime4bytes) ^ s) >> @as(u5, @intCast(shift));
}

fn ZSTD_hash5(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 40)) *% prime5bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 40)) *% prime5bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn ZSTD_hash6(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 48)) *% prime6bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 48)) *% prime6bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn ZSTD_hash7(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 56)) *% prime7bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 56)) *% prime7bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn ZSTD_hash8(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast(u *% prime8bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u *% prime8bytes) ^ s) >> @as(u6, @intCast(shift))));
}

fn ZSTD_hashPtr(p: [*]const u8, hBits: u32, mls: u32) usize {
    // Read 8 bytes regardless of mls, as in the C implementation
    const u = std.mem.readInt(u64, p[0..8], .little);
    return switch (mls) {
        4 => ZSTD_hash4(@truncate(u), hBits, 0),
        5 => ZSTD_hash5(u, hBits, 0),
        6 => ZSTD_hash6(u, hBits, 0),
        7 => ZSTD_hash7(u, hBits, 0),
        8 => ZSTD_hash8(u, hBits, 0),
        else => unreachable,
    };
}

/// Count matching bytes
fn ZSTD_count(ip: [*]const u8, match: [*]const u8, iend: [*]const u8) usize {
    var ip_ptr = ip;
    var match_ptr = match;
    while (@intFromPtr(ip_ptr) < @intFromPtr(iend) and ip_ptr[0] == match_ptr[0]) {
        ip_ptr += 1;
        match_ptr += 1;
    }
    return @intFromPtr(ip_ptr) - @intFromPtr(ip);
}

/// Memory operations (equivalent to mem.h)
fn MEM_writeLE32(ptr: [*]u8, val: u32) void {
    std.mem.writeInt(u32, ptr[0..4], val, .little);
}

fn MEM_writeLE16(ptr: [*]u8, val: u16) void {
    std.mem.writeInt(u16, ptr[0..2], val, .little);
}

fn MEM_writeLE24(ptr: [*]u8, val: u32) void {
    ptr[0] = @truncate(val);
    ptr[1] = @truncate(val >> 8);
    ptr[2] = @truncate(val >> 16);
}

fn MEM_readLE32(ptr: [*]const u8) u32 {
    return std.mem.readInt(u32, ptr[0..4], .little);
}

/// Store sequence in SeqStore
fn ZSTD_storeSeq(seqStore: *SeqStore, litLength: usize, literals: [*]const u8, litLimit: [*]const u8, offBase: i32, matchLength: usize) void {
    const litEnd = literals + litLength;
    const litLimit_w = litLimit - 16; // WILDCOPY_OVERLENGTH

    // Copy literals
    if (@intFromPtr(litEnd) <= @intFromPtr(litLimit_w)) {
        // Use memcpy for common case
        @memcpy(seqStore.litStart[seqStore.lit .. seqStore.lit + litLength], literals[0..litLength]);
    } else {
        // Safe copy
        const toCopy = @min(litLength, @intFromPtr(litLimit) - @intFromPtr(literals));
        @memcpy(seqStore.litStart[seqStore.lit .. seqStore.lit + toCopy], literals[0..toCopy]);
    }
    seqStore.lit += litLength;

    const mlBase: u16 = if (matchLength >= MINMATCH) @intCast(matchLength - MINMATCH) else 0;

    // Store sequence
    seqStore.sequencesStart[seqStore.sequences] = SeqDef{
        .offBase = offBase,
        .litLength = @intCast(litLength),
        .mlBase = mlBase,
    };
    seqStore.sequences += 1;
}

/// Calculate maximum number of sequences for a block
fn ZSTD_maxNbSeq(blockSize: usize, minMatch: u32, useSequenceProducer: bool) usize {
    const divider: u32 = if (minMatch == 3 or useSequenceProducer) 3 else 4;
    return blockSize / divider;
}

/// Update rep array
fn ZSTD_updateRep(rep: *[ZSTD_REP_NUM]u32, offBase: i32, ll0: u32) void {
    const OFFBASE_IS_OFFSET = offBase > 0;
    if (OFFBASE_IS_OFFSET) { // full offset
        rep[2] = rep[1];
        rep[1] = rep[0];
        rep[0] = @intCast(offBase - ZSTD_REP_NUM);
    } else {
        // repcode
        const repCode = -offBase;
        if (repCode > 0) {
            const repIndex = @as(usize, @intCast(repCode - 1));
            const repOffset = rep[repIndex];
            rep[2] = rep[1];
            rep[1] = rep[0];
            rep[0] = repOffset;
        }
    }
    _ = ll0; // unused for now
}

/// Fill hash table
fn ZSTD_fillHashTable(ms: *ZSTD_MatchState_t, src: []const u8) void {
    const cParams = ms.cParams;
    const hashTable = ms.hashTable.ptr;
    const hBits = cParams.hashLog;
    const mls = cParams.minMatch;
    const base = src.ptr;
    var ip = base + ms.nextToUpdate;
    const iend = src.ptr + src.len - HASH_READ_SIZE;

    while (@intFromPtr(ip) < @intFromPtr(iend)) {
        const curr = @intFromPtr(ip) - @intFromPtr(base);
        const hash = ZSTD_hashPtr(ip, hBits, mls);
        hashTable[hash] = @intCast(curr);
        ip += 1;
    }
    ms.nextToUpdate = @intCast(@intFromPtr(ip) - @intFromPtr(base));
}

/// Compress block using fast strategy
fn ZSTD_compressBlock_fast(ms: *ZSTD_MatchState_t, seqStore: *SeqStore, rep: *[ZSTD_REP_NUM]u32, src: []const u8) usize {
    const cParams = ms.cParams;
    const hashTable = ms.hashTable.ptr;
    const hlog = cParams.hashLog;
    const mls = cParams.minMatch;
    const base = src.ptr;
    const istart = src.ptr;
    const iend = src.ptr + src.len;
    const ilimit = iend - HASH_READ_SIZE;

    var anchor = istart;
    var ip = istart;

    // Initialize window
    ms.window.base = base;
    ms.window.nextSrc = istart;

    // Fill hash table
    ZSTD_fillHashTable(ms, src);

    while (@intFromPtr(ip) < @intFromPtr(ilimit)) {
        var matchIdx: u32 = 0;
        var mLength: usize = 0;
        var offcode: u32 = 0;

        // Hash current position
        const hash = ZSTD_hashPtr(ip, hlog, mls);
        matchIdx = hashTable[hash];
        hashTable[hash] = @intCast(@intFromPtr(ip) - @intFromPtr(base));

        // Check for match
        if (matchIdx > 0 and matchIdx < @intFromPtr(ip) - @intFromPtr(base)) {
            const match = base + matchIdx;
            if (MEM_readLE32(ip) == MEM_readLE32(match)) {
                // Count match length
                mLength = ZSTD_count(ip + 4, match + 4, iend);
                mLength += 4;

                // Calculate offset
                const offset = @intFromPtr(ip) - @intFromPtr(match);
                offcode = @intCast(offset);

                // Store sequence
                const litLength = @intFromPtr(ip) - @intFromPtr(anchor);
                ZSTD_storeSeq(seqStore, litLength, anchor, iend, @intCast(offcode), mLength);
                ZSTD_updateRep(rep, @intCast(offcode), 0);

                ip += mLength;
                anchor = ip;
                continue;
            }
        }

        ip += 1;
    }

    // Store remaining literals as sequence with matchLength = 0
    const litLength = @intFromPtr(iend) - @intFromPtr(anchor);
    if (litLength > 0) {
        ZSTD_storeSeq(seqStore, litLength, anchor, iend, 0, 0);
    }

    return @intFromPtr(iend) - @intFromPtr(anchor); // Return literals size
}

/// Frame header size max
pub const ZSTD_FRAMEHEADERSIZE_MAX = 18;

/// Block header size
pub const ZSTD_BLOCKHEADERSIZE = 3;

/// Frame format
pub const ZSTD_format_e = enum {
    f_zstd1,
    f_zstd1_magicless,
};

/// Compression parameters
pub const ZSTD_compressionParameters = struct {
    windowLog: u32,
    chainLog: u32,
    hashLog: u32,
    searchLog: u32,
    minMatch: u32,
    targetLength: u32,
    strategy: ZSTD_strategy,
    hashLog3: u32, // for 3-byte matches
};

pub const ZSTD_strategy = enum {
    fast,
    dfast,
    greedy,
    lazy,
    lazy2,
    btlazy2,
    btopt,
    btultra,
    btultra2,
};

/// Frame parameters
pub const ZSTD_frameParameters = struct {
    contentSizeFlag: bool,
    checksumFlag: bool,
    noDictIDFlag: bool,
};

/// CCtx parameters
pub const ZSTD_CCtx_params = struct {
    format: ZSTD_format_e,
    cParams: ZSTD_compressionParameters,
    fParams: ZSTD_frameParameters,
    compressionLevel: i32,
    // TODO: Add more fields as needed
};

/// Create compression context
pub const ZSTD_CCtx = struct {
    stage: ZSTD_compressionStage_e,
    requestedParams: ZSTD_CCtx_params,
    appliedParams: ZSTD_CCtx_params,
    workspace: []u8,
    allocator: mem.Allocator,
    dictID: u32,
    dictContentSize: usize,
    blockSizeMax: usize,
    pledgedSrcSizePlusOne: u64,
    consumedSrcSize: u64,
    producedCSize: u64,
    isFirstBlock: bool,
    seqStore: SeqStore,
    matchState: ?ZSTD_MatchState_t,
    rep: [ZSTD_REP_NUM]u32,

    const Self = @This();

    pub fn init(allocator: mem.Allocator) !Self {
        // Initialize with default parameters
        const defaultCParams = ZSTD_compressionParameters{
            .windowLog = 23,
            .chainLog = 0,
            .hashLog = 0,
            .searchLog = 0,
            .minMatch = 4,
            .targetLength = 0,
            .strategy = .fast,
            .hashLog3 = 0,
        };

        const defaultFParams = ZSTD_frameParameters{
            .contentSizeFlag = true,
            .checksumFlag = false,
            .noDictIDFlag = false,
        };

        const defaultParams = ZSTD_CCtx_params{
            .format = .f_zstd1,
            .cParams = defaultCParams,
            .fParams = defaultFParams,
            .compressionLevel = ZSTD_CLEVEL_DEFAULT,
        };

        return Self{
            .stage = .created,
            .requestedParams = defaultParams,
            .appliedParams = defaultParams,
            .workspace = try allocator.alloc(u8, 1024 * 1024), // 1MB workspace for now
            .allocator = allocator,
            .dictID = 0,
            .dictContentSize = 0,
            .blockSizeMax = ZSTD_BLOCKSIZE_MAX,
            .pledgedSrcSizePlusOne = 0,
            .consumedSrcSize = 0,
            .producedCSize = 0,
            .isFirstBlock = true,
            .seqStore = SeqStore.init(allocator),
            .matchState = null,
            .rep = [_]u32{0} ** ZSTD_REP_NUM,
        };
    }

    pub fn deinit(self: *Self) void {
        self.seqStore.deinit();
        if (self.matchState) |*ms| {
            ms.deinit();
        }
        self.allocator.free(self.workspace);
    }
};

pub const ZSTD_compressionStage_e = enum {
    created,
    init,
    ongoing,
    ending,
};

/// Create compression context
pub fn ZSTD_createCCtx() !*ZSTD_CCtx {
    const ctx = try std.heap.page_allocator.create(ZSTD_CCtx);
    ctx.* = try ZSTD_CCtx.init(std.heap.page_allocator);
    return ctx;
}

/// Free compression context
pub fn ZSTD_freeCCtx(cctx: ?*ZSTD_CCtx) void {
    if (cctx) |ctx| {
        ctx.deinit();
        std.heap.page_allocator.destroy(ctx);
    }
}

/// Reset CCtx parameters
pub fn ZSTD_CCtx_reset(cctx: *ZSTD_CCtx, reset: ZSTD_ResetDirective) !void {
    _ = cctx;
    _ = reset;
    // TODO: Implement parameter reset
}

pub const ZSTD_ResetDirective = enum {
    reset_session_only,
    reset_parameters,
    reset_session_and_parameters,
};

/// Set compression parameters
pub fn ZSTD_CCtx_setParameter(cctx: *ZSTD_CCtx, param: ZSTD_cParameter, value: i32) !void {
    _ = cctx;
    _ = param;
    _ = value;
    // TODO: Implement parameter setting
}

pub const ZSTD_cParameter = enum {
    c_compressionLevel,
    c_windowLog,
    c_hashLog,
    c_chainLog,
    c_searchLog,
    c_minMatch,
    c_targetLength,
    c_strategy,
    // TODO: Add more parameters
};

/// Compress data
pub fn ZSTD_compress(
    dst: []u8,
    src: []const u8,
    compression_level: i32,
) Error!usize {
    var ctx = try ZSTD_CCtx.init(std.heap.page_allocator);
    defer ctx.deinit();

    return ZSTD_compressCCtx(&ctx, dst, src, compression_level);
}

/// Compress data using context
pub fn ZSTD_compressCCtx(
    cctx: *ZSTD_CCtx,
    dst: []u8,
    src: []const u8,
    compression_level: i32,
) Error!usize {
    // Set compression level
    try ZSTD_CCtx_setParameter(cctx, .c_compressionLevel, compression_level);

    // Reset for new compression
    try ZSTD_CCtx_reset(cctx, .reset_session_only);

    // Begin compression
    const beginResult = try ZSTD_compressBegin(cctx, compression_level);
    if (beginResult != 0) {
        return Error.Generic;
    }

    // Compress the data
    const compressResult = try ZSTD_compressEnd(cctx, dst, src);
    return compressResult;
}

/// Begin compression
pub fn ZSTD_compressBegin(cctx: *ZSTD_CCtx, compressionLevel: i32) !usize {
    // Set up parameters based on compression level
    const params = ZSTD_getCParams(compressionLevel, ZSTD_CONTENTSIZE_UNKNOWN, 0);
    cctx.appliedParams.cParams = params;
    cctx.appliedParams.compressionLevel = compressionLevel;

    // Calculate block size and sequence counts
    const windowSize = if (params.windowLog < 31) @as(usize, 1) << @intCast(params.windowLog) else ZSTD_MAX_INPUT_SIZE;
    cctx.blockSizeMax = @min(ZSTD_BLOCKSIZE_MAX, windowSize);
    const maxNbSeq = ZSTD_maxNbSeq(cctx.blockSizeMax, params.minMatch, false);

    // Initialize seqStore
    cctx.seqStore.deinit();
    cctx.seqStore.sequencesStart = try cctx.allocator.alloc(SeqDef, maxNbSeq);
    cctx.seqStore.sequences = 0;
    cctx.seqStore.litStart = try cctx.allocator.alloc(u8, cctx.blockSizeMax + 16); // WILDCOPY_OVERLENGTH
    cctx.seqStore.lit = 0;
    cctx.seqStore.llCode = try cctx.allocator.alloc(u8, maxNbSeq);
    cctx.seqStore.mlCode = try cctx.allocator.alloc(u8, maxNbSeq);
    cctx.seqStore.ofCode = try cctx.allocator.alloc(u8, maxNbSeq);
    cctx.seqStore.maxNbSeq = maxNbSeq;
    cctx.seqStore.maxNbLit = cctx.blockSizeMax;

    // Initialize match state
    if (cctx.matchState) |*ms| {
        ms.deinit();
    }
    cctx.matchState = try ZSTD_MatchState_t.init(cctx.allocator, params);

    // Initialize for compression
    cctx.stage = .init;
    cctx.pledgedSrcSizePlusOne = 0; // Unknown size
    cctx.consumedSrcSize = 0;
    cctx.producedCSize = 0;
    cctx.isFirstBlock = true;

    return 0;
}

/// End compression
pub fn ZSTD_compressEnd(cctx: *ZSTD_CCtx, dst: []u8, src: []const u8) !usize {
    if (cctx.stage != .init) {
        return Error.StageWrong;
    }

    if (cctx.matchState == null) {
        return Error.InitMissing;
    }

    var op = dst.ptr;
    const oend = dst.ptr + dst.len;

    // Write frame header
    const fhSize = try ZSTD_writeFrameHeader(op[0..@min(ZSTD_FRAMEHEADERSIZE_MAX, @intFromPtr(oend) - @intFromPtr(op))], &cctx.appliedParams, src.len, 0);
    op += fhSize;

    // Compress the block
    const compressedSize = ZSTD_compressBlock_fast(&cctx.matchState.?, &cctx.seqStore, &cctx.rep, src);
    _ = compressedSize; // For now, ignore the result

    // For now, write as uncompressed block
    const blockSize = @min(cctx.blockSizeMax, src.len);
    if (blockSize > 0) {
        const compressedBlockSize = try ZSTD_compressBlock_simple(op[0 .. @intFromPtr(oend) - @intFromPtr(op)], src[0..blockSize]);
        op += compressedBlockSize;
    }

    // Write last empty block
    const lastBlockSize = try ZSTD_writeLastEmptyBlock(op[0 .. @intFromPtr(oend) - @intFromPtr(op)]);
    op += lastBlockSize;

    cctx.stage = .ending;
    return @intFromPtr(op) - @intFromPtr(dst.ptr);
}

/// Get compression parameters for a level
pub fn ZSTD_getCParams(compressionLevel: i32, srcSize: u64, dictSize: usize) ZSTD_compressionParameters {
    _ = dictSize;

    // Simplified parameter selection based on C implementation
    const level = std.math.clamp(compressionLevel, 1, 22);

    // Determine table based on srcSize (simplified)
    const tableID: u32 = if (srcSize <= 16 * 1024) 2 else if (srcSize <= 128 * 1024) 1 else 0;

    return switch (tableID) {
        0 => switch (level) { // srcSize > 256 KB
            1 => .{ .windowLog = 19, .chainLog = 12, .hashLog = 13, .searchLog = 1, .minMatch = 6, .targetLength = 1, .strategy = .fast, .hashLog3 = 0 },
            2 => .{ .windowLog = 20, .chainLog = 15, .hashLog = 16, .searchLog = 1, .minMatch = 6, .targetLength = 0, .strategy = .fast, .hashLog3 = 0 },
            3 => .{ .windowLog = 21, .chainLog = 16, .hashLog = 17, .searchLog = 1, .minMatch = 5, .targetLength = 0, .strategy = .dfast, .hashLog3 = 0 },
            4 => .{ .windowLog = 21, .chainLog = 18, .hashLog = 18, .searchLog = 1, .minMatch = 5, .targetLength = 0, .strategy = .dfast, .hashLog3 = 0 },
            else => .{ .windowLog = 23, .chainLog = 23, .hashLog = 23, .searchLog = 2, .minMatch = 4, .targetLength = 0, .strategy = .lazy2, .hashLog3 = 16 },
        },
        1 => switch (level) { // srcSize <= 256 KB
            1 => .{ .windowLog = 18, .chainLog = 12, .hashLog = 13, .searchLog = 1, .minMatch = 5, .targetLength = 1, .strategy = .fast, .hashLog3 = 0 },
            2 => .{ .windowLog = 18, .chainLog = 13, .hashLog = 14, .searchLog = 1, .minMatch = 6, .targetLength = 0, .strategy = .fast, .hashLog3 = 0 },
            3 => .{ .windowLog = 18, .chainLog = 16, .hashLog = 16, .searchLog = 1, .minMatch = 4, .targetLength = 0, .strategy = .dfast, .hashLog3 = 0 },
            4 => .{ .windowLog = 18, .chainLog = 16, .hashLog = 17, .searchLog = 3, .minMatch = 5, .targetLength = 2, .strategy = .greedy, .hashLog3 = 0 },
            else => .{ .windowLog = 18, .chainLog = 19, .hashLog = 19, .searchLog = 7, .minMatch = 4, .targetLength = 12, .strategy = .btlazy2, .hashLog3 = 0 },
        },
        2 => switch (level) { // srcSize <= 128 KB
            1 => .{ .windowLog = 17, .chainLog = 12, .hashLog = 12, .searchLog = 1, .minMatch = 5, .targetLength = 1, .strategy = .fast, .hashLog3 = 0 },
            2 => .{ .windowLog = 17, .chainLog = 12, .hashLog = 13, .searchLog = 1, .minMatch = 6, .targetLength = 0, .strategy = .fast, .hashLog3 = 0 },
            3 => .{ .windowLog = 17, .chainLog = 15, .hashLog = 16, .searchLog = 2, .minMatch = 5, .targetLength = 0, .strategy = .dfast, .hashLog3 = 0 },
            4 => .{ .windowLog = 17, .chainLog = 17, .hashLog = 17, .searchLog = 2, .minMatch = 4, .targetLength = 0, .strategy = .dfast, .hashLog3 = 0 },
            else => .{ .windowLog = 17, .chainLog = 18, .hashLog = 17, .searchLog = 7, .minMatch = 4, .targetLength = 12, .strategy = .btlazy2, .hashLog3 = 0 },
        },
        else => unreachable,
    };
}

/// Write frame header
fn ZSTD_writeFrameHeader(dst: []u8, params: *const ZSTD_CCtx_params, pledgedSrcSize: u64, dictID: u32) !usize {
    if (dst.len < ZSTD_FRAMEHEADERSIZE_MAX) {
        return Error.DstSizeTooSmall;
    }

    var op = dst.ptr;
    const dictIDSizeCodeLength = @as(u32, @intFromBool(dictID > 0)) + @as(u32, @intFromBool(dictID >= 256)) + @as(u32, @intFromBool(dictID >= 65536));
    const dictIDSizeCode = if (params.fParams.noDictIDFlag) 0 else dictIDSizeCodeLength;
    const checksumFlag = @as(u32, @intFromBool(params.fParams.checksumFlag));
    const windowSize = @as(u32, 1) << @as(u5, @intCast(params.cParams.windowLog));
    const singleSegment = params.fParams.contentSizeFlag and (windowSize >= pledgedSrcSize);
    const windowLogByte = (@as(u8, @intCast(params.cParams.windowLog)) - @as(u8, ZSTD_WINDOWLOG_ABSOLUTEMIN)) << 3;
    const fcsCode = if (params.fParams.contentSizeFlag)
        @as(u32, @intFromBool(pledgedSrcSize >= 256)) + @as(u32, @intFromBool(pledgedSrcSize >= 65536 + 256)) + @as(u32, @intFromBool(pledgedSrcSize >= 0xFFFFFFFF))
    else
        0;
    const frameHeaderDescriptionByte = @as(u8, @intCast(dictIDSizeCode | (checksumFlag << 2) | (@as(u32, @intFromBool(singleSegment)) << 5) | (fcsCode << 6)));

    var pos: usize = 0;

    // Magic number
    if (params.format == .f_zstd1) {
        MEM_writeLE32(op, ZSTD_MAGICNUMBER);
        pos = 4;
    }

    op[pos] = frameHeaderDescriptionByte;
    pos += 1;

    if (!singleSegment) {
        op[pos] = windowLogByte;
        pos += 1;
    }

    // Dictionary ID
    switch (dictIDSizeCode) {
        0 => {},
        1 => {
            op[pos] = @truncate(dictID);
            pos += 1;
        },
        2 => {
            MEM_writeLE16(op + pos, @truncate(dictID));
            pos += 2;
        },
        3 => {
            MEM_writeLE32(op + pos, dictID);
            pos += 4;
        },
        else => unreachable,
    }

    // Content size
    switch (fcsCode) {
        0 => if (singleSegment) {
            op[pos] = @truncate(pledgedSrcSize);
            pos += 1;
        },
        1 => {
            MEM_writeLE16(op + pos, @truncate(pledgedSrcSize - 256));
            pos += 2;
        },
        2 => {
            MEM_writeLE32(op + pos, @truncate(pledgedSrcSize));
            pos += 4;
        },
        3 => {
            MEM_writeLE32(op + pos, @truncate(pledgedSrcSize));
            MEM_writeLE32(op + pos + 4, @truncate(pledgedSrcSize >> 32));
            pos += 8;
        },
        else => unreachable,
    }

    return pos;
}

/// Write last empty block
fn ZSTD_writeLastEmptyBlock(dst: []u8) !usize {
    if (dst.len < ZSTD_BLOCKHEADERSIZE) {
        return Error.DstSizeTooSmall;
    }

    // Last block + raw block type + 0 size
    const cBlockHeader24: u32 = 1 | (@as(u32, 0) << 1); // bt_raw = 0
    MEM_writeLE24(dst.ptr, cBlockHeader24);
    return ZSTD_BLOCKHEADERSIZE;
}

/// Simple block compression (placeholder)
fn ZSTD_compressBlock_simple(dst: []u8, src: []const u8) !usize {
    // For now, just write as uncompressed block
    if (dst.len < ZSTD_BLOCKHEADERSIZE + src.len) {
        return Error.DstSizeTooSmall;
    }

    var op = dst.ptr;

    // Block header: not last block + raw block type + size
    const cBlockHeader24: u32 = 0 | (@as(u32, 0) << 1) | (@as(u32, @intCast(src.len)) << 3); // bt_raw = 0
    MEM_writeLE24(op, cBlockHeader24);
    op += ZSTD_BLOCKHEADERSIZE;

    // Copy data
    @memcpy(op[0..src.len], src);
    return ZSTD_BLOCKHEADERSIZE + src.len;
}

/// Get maximum compressed size
pub fn ZSTD_compressBound(src_size: usize) usize {
    if (src_size >= ZSTD_MAX_INPUT_SIZE) {
        return 0;
    }
    const bound = src_size + (src_size >> 8) + if (src_size < (128 << 10))
        ((128 << 10) - src_size) >> 11
    else
        0;
    return bound;
}

/// Check if result is an error
pub fn ZSTD_isError(result: usize) bool {
    return result > ZSTD_MAX_INPUT_SIZE;
}

/// Get error code from result
pub fn ZSTD_getErrorCode(result: usize) ZSTD_ErrorCode {
    if (!ZSTD_isError(result)) {
        return .no_error;
    }
    // TODO: Implement proper error code mapping
    return .generic;
}

/// Error codes enum
pub const ZSTD_ErrorCode = enum {
    no_error,
    generic,
    prefix_unknown,
    version_unsupported,
    frameParameter_unsupported,
    frameParameter_windowTooLarge,
    corruption_detected,
    checksum_wrong,
    literals_headerWrong,
    dictionary_corrupted,
    dictionary_wrong,
    bad_arguments,
    maxCode,
};

/// Get error name
pub fn ZSTD_getErrorName(result: usize) []const u8 {
    const err_code = ZSTD_getErrorCode(result);
    return switch (err_code) {
        .no_error => "No error detected",
        .generic => "Error (generic)",
        .prefix_unknown => "Unknown frame descriptor",
        .version_unsupported => "Version not supported",
        .frameParameter_unsupported => "Unsupported frame parameter",
        .frameParameter_windowTooLarge => "Frame parameter window too large",
        .corruption_detected => "Corrupted block detected",
        .checksum_wrong => "Restored data doesn't match checksum",
        .literals_headerWrong => "Invalid literals header",
        .dictionary_corrupted => "Dictionary is corrupted",
        .dictionary_wrong => "Dictionary mismatch",
        .bad_arguments => "Invalid parameter",
        .maxCode => "Max error code",
    };
}

/// Get minimum compression level
pub fn ZSTD_minCLevel() i32 {
    return 1;
}

/// Get maximum compression level
pub fn ZSTD_maxCLevel() i32 {
    return 22;
}

/// Get default compression level
pub fn ZSTD_defaultCLevel() i32 {
    return ZSTD_CLEVEL_DEFAULT;
}

/// Version number
pub fn ZSTD_versionNumber() u32 {
    return ZSTD_VERSION_MAJOR * 100 * 100 + ZSTD_VERSION_MINOR * 100 + ZSTD_VERSION_RELEASE;
}

/// Version string
pub fn ZSTD_versionString() []const u8 {
    return "1.6.0";
}

// Sequence storage
const SeqDef = struct {
    offBase: i32, // offBase == Offset + ZSTD_REP_NUM, or repcode 1,2,3
    litLength: u16,
    mlBase: u16, // mlBase == matchLength - MINMATCH
};

const SeqStore = struct {
    sequencesStart: []SeqDef,
    sequences: usize, // index to end of sequences
    litStart: []u8,
    lit: usize, // index to end of literals
    llCode: []u8,
    mlCode: []u8,
    ofCode: []u8,
    maxNbSeq: usize,
    maxNbLit: usize,
    allocator: mem.Allocator,

    fn init(allocator: mem.Allocator) SeqStore {
        return SeqStore{
            .sequencesStart = &[_]SeqDef{},
            .sequences = 0,
            .litStart = &[_]u8{},
            .lit = 0,
            .llCode = &[_]u8{},
            .mlCode = &[_]u8{},
            .ofCode = &[_]u8{},
            .maxNbSeq = 0,
            .maxNbLit = 0,
            .allocator = allocator,
        };
    }

    fn deinit(self: *SeqStore) void {
        if (self.sequencesStart.len > 0) self.allocator.free(self.sequencesStart);
        if (self.litStart.len > 0) self.allocator.free(self.litStart);
        if (self.llCode.len > 0) self.allocator.free(self.llCode);
        if (self.mlCode.len > 0) self.allocator.free(self.mlCode);
        if (self.ofCode.len > 0) self.allocator.free(self.ofCode);
    }
};

// Window management
const ZSTD_window_t = struct {
    nextSrc: [*]const u8, // next block here to continue on current prefix
    base: [*]const u8, // All regular indexes relative to this position
    dictBase: [*]const u8, // extDict indexes relative to this position
    dictLimit: u32, // below that point, need extDict
    lowLimit: u32, // below that point, no more valid data
};

// Match state
const ZSTD_MatchState_t = struct {
    window: ZSTD_window_t,
    loadedDictEnd: u32,
    nextToUpdate: u32,
    hashLog3: u32,
    hashTable: []u32,
    hashTable3: []u32,
    chainTable: []u32,
    cParams: ZSTD_compressionParameters,
    allocator: mem.Allocator,

    fn init(allocator: mem.Allocator, cParams: ZSTD_compressionParameters) !ZSTD_MatchState_t {
        const hashTableSize = @as(usize, 1) << @as(u6, @intCast(cParams.hashLog));
        const hashTable3Size = @as(usize, 1) << @as(u6, @intCast(cParams.hashLog3));
        const chainTableSize = @as(usize, 1) << @as(u6, @intCast(cParams.chainLog));

        return ZSTD_MatchState_t{
            .window = ZSTD_window_t{
                .nextSrc = undefined,
                .base = undefined,
                .dictBase = undefined,
                .dictLimit = 0,
                .lowLimit = 0,
            },
            .loadedDictEnd = 0,
            .nextToUpdate = 0,
            .hashLog3 = cParams.hashLog3,
            .hashTable = try allocator.alloc(u32, hashTableSize),
            .hashTable3 = try allocator.alloc(u32, hashTable3Size),
            .chainTable = try allocator.alloc(u32, chainTableSize),
            .cParams = cParams,
            .allocator = allocator,
        };
    }

    fn deinit(self: *ZSTD_MatchState_t) void {
        self.allocator.free(self.hashTable);
        self.allocator.free(self.hashTable3);
        self.allocator.free(self.chainTable);
    }
};

// TODO: Implement decompression functions
// pub fn ZSTD_decompress() !usize { ... }
// pub fn ZSTD_createDCtx() !*ZSTD_DCtx { ... }
// etc.

// TODO: Implement all the compression strategies
// fn ZSTD_compressBlock_fast(...) usize { ... }
// fn ZSTD_compressBlock_greedy(...) usize { ... }
// etc.

// TODO: Implement FSE and Huffman coding
// TODO: Implement match finding algorithms
// TODO: Implement dictionary support
// TODO: Implement streaming compression
// TODO: Implement multi-threading support

test "basic compression roundtrip" {
    const src = "Hello, World! This is a test string for compression.";
    var dst: [1024]u8 = undefined;

    const compressed_size = try ZSTD_compress(&dst, src, ZSTD_CLEVEL_DEFAULT);
    try std.testing.expect(compressed_size > 0);
    try std.testing.expect(compressed_size <= ZSTD_compressBound(src.len));

    var decomp_input = std.Io.Reader.fixed(dst[0..compressed_size]);
    var decomp_buf: [262144]u8 = undefined;
    var decompress: std.compress.zstd.Decompress = .init(
        &decomp_input,
        &decomp_buf,
        .{ .window_len = 131072 },
    );
    try decompress.reader.fillMore();
    const decompressed = decompress.reader.buffered();
    try std.testing.expect(decompressed.len == src.len);
    try std.testing.expect(std.mem.eql(u8, decompressed, src));
}

test "compress bound" {
    try std.testing.expect(ZSTD_compressBound(0) == 64);
    try std.testing.expect(ZSTD_compressBound(100) > 100);
    try std.testing.expect(ZSTD_compressBound(ZSTD_MAX_INPUT_SIZE) == 0);
}
test "version" {
    try std.testing.expect(ZSTD_versionNumber() == 10600);
    try std.testing.expect(std.mem.eql(u8, ZSTD_versionString(), "1.6.0"));
}

pub const FuzzContext = struct {
    src_buf: []u8,
    dst_buf: []u8,
    decomp_buf: []u8,
    pub fn testOne(self: @This(), smith: *std.testing.Smith) !void {
        const src_len = smith.slice(self.src_buf);
        const src = self.src_buf[0..src_len];

        const compressed_size = try ZSTD_compress(self.dst_buf, src, ZSTD_CLEVEL_DEFAULT);
        try std.testing.expect(compressed_size > 0);
        std.testing.expect(compressed_size <= ZSTD_compressBound(src.len)) catch |err| {
            std.log.err("error {}", .{err});
            std.log.err("expected: <={x}", .{ZSTD_compressBound(src.len)});
            std.log.err("got: {x}", .{compressed_size});
            return;
        };

        var decomp_input = std.Io.Reader.fixed(self.dst_buf[0..compressed_size]);
        var decompress: std.compress.zstd.Decompress = .init(&decomp_input, self.decomp_buf, .{ .window_len = 131072 });
        try decompress.reader.fillMore();
        const decompressed = decompress.reader.buffered();
        std.testing.expect(std.mem.eql(u8, decompressed, src)) catch |err| {
            std.log.err("error {}", .{err});
            std.log.err("expected: {x}", .{src});
            std.log.err("got: {x}", .{decompressed});
            return;
        };
    }
};

test "fuzz compression roundtrip" {
    const ctx = FuzzContext{
        .src_buf = try std.testing.allocator.alloc(u8, 16 * std.math.pow(usize, 2, 20)),
        .dst_buf = try std.testing.allocator.alloc(u8, 16 * std.math.pow(usize, 2, 20)),
        .decomp_buf = try std.testing.allocator.alloc(u8, 16 * std.math.pow(usize, 2, 20)),
    };
    defer {
        std.testing.allocator.free(ctx.src_buf);
        std.testing.allocator.free(ctx.dst_buf);
        std.testing.allocator.free(ctx.decomp_buf);
    }
    try std.testing.fuzz(ctx, FuzzContext.testOne, .{});
}
