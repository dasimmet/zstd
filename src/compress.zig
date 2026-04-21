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

/// Magic numbers
pub const MAGICNUMBER = 0xFD2FB528;
pub const MAGIC_DICTIONARY = 0xEC30A437;
pub const MAGIC_SKIPPABLE_START = 0x184D2A50;

/// Constants
pub const CONTENTSIZE_UNKNOWN = math.maxInt(u64);
pub const CONTENTSIZE_ERROR = math.maxInt(u64) - 1;

pub const MAX_INPUT_SIZE = if (@sizeOf(usize) == 8) 0xFF00FF00FF00FF00 else 0xFF00FF00;

/// Default compression level
pub const CLEVEL_DEFAULT = 3;

/// Block size limits
pub const BLOCKSIZELOG_MAX = 17;
pub const BLOCKSIZE_MAX = 1 << BLOCKSIZELOG_MAX;

/// Window log limits
pub const WINDOWLOG_ABSOLUTEMIN = 10;

/// Sequence constants
pub const REP_NUM = 3;
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
fn hash3(u: u32, h: u32, s: u32) u32 {
    return (((u << (32 - 24)) *% prime3bytes) ^ s) >> (32 - h);
}

fn hash4(u: u32, h: u32, s: u32) u32 {
    if (h >= 32) return (u *% prime4bytes) ^ s;
    const shift = 32 - h;
    return ((u *% prime4bytes) ^ s) >> @as(u5, @intCast(shift));
}

fn hash5(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 40)) *% prime5bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 40)) *% prime5bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn hash6(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 48)) *% prime6bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 48)) *% prime6bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn hash7(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast((u << (64 - 56)) *% prime7bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u << (64 - 56)) *% prime7bytes) ^ s) >> @as(u6, @intCast(shift)));
}

fn hash8(u: u64, h: u32, s: u64) usize {
    if (h >= 64) return @intCast(u *% prime8bytes ^ s);
    const shift = 64 - h;
    return @intCast((((u *% prime8bytes) ^ s) >> @as(u6, @intCast(shift))));
}

fn hashPtr(p: [*]const u8, hBits: u32, mls: u32) usize {
    // Read 8 bytes regardless of mls, as in the C implementation
    const u = std.mem.readInt(u64, p[0..8], .little);
    return switch (mls) {
        4 => hash4(@truncate(u), hBits, 0),
        5 => hash5(u, hBits, 0),
        6 => hash6(u, hBits, 0),
        7 => hash7(u, hBits, 0),
        8 => hash8(u, hBits, 0),
        else => unreachable,
    };
}

/// Count matching bytes
fn count(ip: [*]const u8, match: [*]const u8, iend: [*]const u8) usize {
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
fn storeSeq(seqStore: *Sequence.Store, litLength: usize, literals: [*]const u8, litLimit: [*]const u8, offBase: i32, matchLength: usize) void {
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
    seqStore.sequencesStart[seqStore.sequences] = Sequence{
        .offBase = offBase,
        .litLength = @intCast(litLength),
        .mlBase = mlBase,
    };
    seqStore.sequences += 1;
}

/// Calculate maximum number of sequences for a block
fn maxNbSeq(blockSize: usize, minMatch: u32, useSequenceProducer: bool) usize {
    const divider: u32 = if (minMatch == 3 or useSequenceProducer) 3 else 4;
    return blockSize / divider;
}

/// Update rep array
fn updateRep(rep: *[REP_NUM]u32, offBase: i32, ll0: u32) void {
    const OFFBASE_IS_OFFSET = offBase > 0;
    if (OFFBASE_IS_OFFSET) { // full offset
        rep[2] = rep[1];
        rep[1] = rep[0];
        rep[0] = @intCast(offBase - REP_NUM);
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
fn fillHashTable(ms: *MatchState, src: []const u8) void {
    const cParams = ms.cParams;
    const hashTable = ms.hashTable.ptr;
    const hBits = cParams.hashLog;
    const mls = cParams.minMatch;
    const base = src.ptr;
    var ip = base + ms.nextToUpdate;
    const iend = src.ptr + src.len - HASH_READ_SIZE;

    while (@intFromPtr(ip) < @intFromPtr(iend)) {
        const curr = @intFromPtr(ip) - @intFromPtr(base);
        const hash = hashPtr(ip, hBits, mls);
        hashTable[hash] = @intCast(curr);
        ip += 1;
    }
    ms.nextToUpdate = @intCast(@intFromPtr(ip) - @intFromPtr(base));
}

/// Compress block using fast strategy
fn compressBlock_fast(ms: *MatchState, seqStore: *Sequence.Store, rep: *[REP_NUM]u32, src: []const u8) usize {
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
    fillHashTable(ms, src);

    while (@intFromPtr(ip) < @intFromPtr(ilimit)) {
        var matchIdx: u32 = 0;
        var mLength: usize = 0;
        var offcode: u32 = 0;

        // Hash current position
        const hash = hashPtr(ip, hlog, mls);
        matchIdx = hashTable[hash];
        hashTable[hash] = @intCast(@intFromPtr(ip) - @intFromPtr(base));

        // Check for match
        if (matchIdx > 0 and matchIdx < @intFromPtr(ip) - @intFromPtr(base)) {
            const match = base + matchIdx;
            if (MEM_readLE32(ip) == MEM_readLE32(match)) {
                // Count match length
                mLength = count(ip + 4, match + 4, iend);
                mLength += 4;

                // Calculate offset
                const offset = @intFromPtr(ip) - @intFromPtr(match);
                offcode = @intCast(offset);

                // Store sequence
                const litLength = @intFromPtr(ip) - @intFromPtr(anchor);
                storeSeq(seqStore, litLength, anchor, iend, @intCast(offcode), mLength);
                updateRep(rep, @intCast(offcode), 0);

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
        storeSeq(seqStore, litLength, anchor, iend, 0, 0);
    }

    return @intFromPtr(iend) - @intFromPtr(anchor); // Return literals size
}

/// Frame header size max
pub const FRAMEHEADERSIZE_MAX = 18;

/// Block header size
pub const BLOCKHEADERSIZE = 3;

pub const Strategy = enum {
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
pub const FrameParameters = struct {
    contentSizeFlag: bool,
    checksumFlag: bool,
    noDictIDFlag: bool,

    const defaults = FrameParameters{
        .contentSizeFlag = true,
        .checksumFlag = false,
        .noDictIDFlag = false,
    };
};

/// Create compression context
pub const Context = struct {
    stage: Stage,
    requestedParams: Parameters,
    appliedParams: Parameters,
    workspace: []u8,
    allocator: mem.Allocator,
    dictID: u32,
    dictContentSize: usize,
    blockSizeMax: usize,
    pledgedSrcSizePlusOne: u64,
    consumedSrcSize: u64,
    producedCSize: u64,
    isFirstBlock: bool,
    seqStore: Sequence.Store,
    matchState: ?MatchState,
    rep: [REP_NUM]u32,

    const Self = @This();

    pub const Stage = enum {
        created,
        init,
        ongoing,
        ending,
    };

    /// CCtx parameters
    pub const Parameters = struct {
        /// Frame format
        pub const Format = enum {
            zstd1,
            zstd1_magicless,
        };

        /// Compression parameters
        pub const Compression = struct {
            windowLog: u32,
            chainLog: u32,
            hashLog: u32,
            searchLog: u32,
            minMatch: u32,
            targetLength: u32,
            strategy: Strategy,
            hashLog3: u32, // for 3-byte matches

            const defaults = Compression{
                .windowLog = 23,
                .chainLog = 0,
                .hashLog = 0,
                .searchLog = 0,
                .minMatch = 4,
                .targetLength = 0,
                .strategy = .fast,
                .hashLog3 = 0,
            };
        };

        format: Format = .zstd1,
        cParams: Compression = .defaults,
        fParams: FrameParameters = .defaults,
        compressionLevel: i32 = CLEVEL_DEFAULT,
    };
    pub fn init(allocator: mem.Allocator) !Self {
        // Initialize with default parameters

        return Self{
            .stage = .created,
            .requestedParams = .{},
            .appliedParams = .{},
            .workspace = try allocator.alloc(u8, 1024 * 1024), // 1MB workspace for now
            .allocator = allocator,
            .dictID = 0,
            .dictContentSize = 0,
            .blockSizeMax = BLOCKSIZE_MAX,
            .pledgedSrcSizePlusOne = 0,
            .consumedSrcSize = 0,
            .producedCSize = 0,
            .isFirstBlock = true,
            .seqStore = Sequence.Store.init(allocator),
            .matchState = null,
            .rep = [_]u32{0} ** REP_NUM,
        };
    }

    pub fn deinit(self: *Self) void {
        self.seqStore.deinit();
        if (self.matchState) |*ms| {
            ms.deinit();
        }
        self.allocator.free(self.workspace);
    }

    pub fn compress(
        cctx: *Context,
        dst: []u8,
        src: []const u8,
        compression_level: i32,
    ) Error!usize {
        // Set compression level
        try setParameter(cctx, .c_compressionLevel, compression_level);

        // Reset for new compression
        try reset(cctx, .reset_session_only);

        // Begin compression
        const beginResult = try cctx.begin(compression_level);
        if (beginResult != 0) {
            return Error.Generic;
        }

        // Compress the data
        const compressResult = try end(cctx, dst, src);
        return compressResult;
    }

    /// Set compression parameters
    pub fn setParameter(cctx: *Context, param: cParameter, value: i32) !void {
        _ = cctx;
        _ = param;
        _ = value;
        // TODO: Implement parameter setting
    }

    /// Reset CCtx parameters
    pub fn reset(cctx: *Context, directive: ResetDirective) !void {
        _ = cctx;
        _ = directive;
        // TODO: Implement parameter reset
    }

    pub fn begin(cctx: *Context, compressionLevel: i32) !usize {
        // Set up parameters based on compression level
        const params = getCParams(compressionLevel, CONTENTSIZE_UNKNOWN, 0);
        cctx.appliedParams.cParams = params;
        cctx.appliedParams.compressionLevel = compressionLevel;

        // Calculate block size and sequence counts
        const windowSize = if (params.windowLog < 31) @as(usize, 1) << @intCast(params.windowLog) else MAX_INPUT_SIZE;
        cctx.blockSizeMax = @min(BLOCKSIZE_MAX, windowSize);
        const maxNbS = maxNbSeq(cctx.blockSizeMax, params.minMatch, false);

        // Initialize seqStore
        cctx.seqStore.deinit();
        cctx.seqStore.sequencesStart = try cctx.allocator.alloc(Sequence, maxNbS);
        cctx.seqStore.sequences = 0;
        cctx.seqStore.litStart = try cctx.allocator.alloc(u8, cctx.blockSizeMax + 16); // WILDCOPY_OVERLENGTH
        cctx.seqStore.lit = 0;
        cctx.seqStore.llCode = try cctx.allocator.alloc(u8, maxNbS);
        cctx.seqStore.mlCode = try cctx.allocator.alloc(u8, maxNbS);
        cctx.seqStore.ofCode = try cctx.allocator.alloc(u8, maxNbS);
        cctx.seqStore.maxNbSeq = maxNbS;
        cctx.seqStore.maxNbLit = cctx.blockSizeMax;

        // Initialize match state
        if (cctx.matchState) |*ms| {
            ms.deinit();
        }
        cctx.matchState = try MatchState.init(cctx.allocator, params);

        // Initialize for compression
        cctx.stage = .init;
        cctx.pledgedSrcSizePlusOne = 0; // Unknown size
        cctx.consumedSrcSize = 0;
        cctx.producedCSize = 0;
        cctx.isFirstBlock = true;

        return 0;
    }

    /// End compression
    pub fn end(cctx: *Context, dst: []u8, src: []const u8) !usize {
        if (cctx.stage != .init) {
            return Error.StageWrong;
        }

        if (cctx.matchState == null) {
            return Error.InitMissing;
        }

        var op = dst.ptr;
        const oend = dst.ptr + dst.len;

        // Write frame header
        const fhSize = try writeFrameHeader(op[0..@min(FRAMEHEADERSIZE_MAX, @intFromPtr(oend) - @intFromPtr(op))], &cctx.appliedParams, src.len, 0);
        op += fhSize;

        // Compress data using match finding
        var srcPos: usize = 0;
        var hasWrittenBlock = false;

        while (srcPos < src.len) {
            const remainingSize = src.len - srcPos;
            const blockSize = @min(cctx.blockSizeMax, remainingSize);
            const isLastBlock = (srcPos + blockSize >= src.len);

            // Try to compress the block
            const blockData = src[srcPos .. srcPos + blockSize];

            // Find matches using fast compression
            _ = compressBlock_fast(&cctx.matchState.?, &cctx.seqStore, &cctx.rep, blockData);

            // Encode the sequences into a compressed block
            const blockCompressed = try encodeCompressedBlock(
                op[0 .. @intFromPtr(oend) - @intFromPtr(op)],
                &cctx.seqStore,
                isLastBlock,
            );

            // If encoding fails or results are not better, use raw block
            const useRawBlock = blockCompressed == 0 or blockCompressed >= blockSize;
            const finalBlockSize = if (useRawBlock)
                try writeLiteralBlock(
                    op[0 .. @intFromPtr(oend) - @intFromPtr(op)],
                    blockData,
                    isLastBlock,
                )
            else
                blockCompressed;

            op += finalBlockSize;
            srcPos += blockSize;
            hasWrittenBlock = true;

            // Reset seqStore for next block
            cctx.seqStore.sequences = 0;
            cctx.seqStore.lit = 0;
        }

        // If we haven't written any block yet (empty input), write an empty final block
        if (!hasWrittenBlock) {
            const emptyBlockSize = try writeLiteralBlock(
                op[0 .. @intFromPtr(oend) - @intFromPtr(op)],
                &[_]u8{},
                true,
            );
            op += emptyBlockSize;
        }

        cctx.stage = .ending;
        return @intFromPtr(op) - @intFromPtr(dst.ptr);
    }
};

/// Create compression context
pub fn ZSTD_createCCtx() !*Context {
    const ctx = try std.heap.page_allocator.create(Context);
    ctx.* = try Context.init(std.heap.page_allocator);
    return ctx;
}

/// Free compression context
pub fn ZSTD_freeCCtx(cctx: ?*Context) void {
    if (cctx) |ctx| {
        ctx.deinit();
        std.heap.page_allocator.destroy(ctx);
    }
}

pub const ResetDirective = enum {
    reset_session_only,
    reset_parameters,
    reset_session_and_parameters,
};

pub const cParameter = enum {
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
    var ctx = try Context.init(std.heap.page_allocator);
    defer ctx.deinit();

    return ctx.compress(dst, src, compression_level);
}

/// Get compression parameters for a level
pub fn getCParams(compressionLevel: i32, srcSize: u64, dictSize: usize) Context.Parameters.Compression {
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
fn writeFrameHeader(dst: []u8, params: *const Context.Parameters, pledgedSrcSize: u64, dictID: u32) !usize {
    if (dst.len < FRAMEHEADERSIZE_MAX) {
        return Error.DstSizeTooSmall;
    }

    var op = dst.ptr;
    const dictIDSizeCodeLength = @as(u32, @intFromBool(dictID > 0)) + @as(u32, @intFromBool(dictID >= 256)) + @as(u32, @intFromBool(dictID >= 65536));
    const dictIDSizeCode = if (params.fParams.noDictIDFlag) 0 else dictIDSizeCodeLength;
    const checksumFlag = @as(u32, @intFromBool(params.fParams.checksumFlag));
    const windowSize = @as(u32, 1) << @as(u5, @intCast(params.cParams.windowLog));
    const singleSegment = params.fParams.contentSizeFlag and (windowSize >= pledgedSrcSize);
    const windowLogByte = (@as(u8, @intCast(params.cParams.windowLog)) - @as(u8, WINDOWLOG_ABSOLUTEMIN)) << 3;
    const fcsCode = if (params.fParams.contentSizeFlag)
        @as(u32, @intFromBool(pledgedSrcSize >= 256)) + @as(u32, @intFromBool(pledgedSrcSize >= 65536 + 256)) + @as(u32, @intFromBool(pledgedSrcSize >= 0xFFFFFFFF))
    else
        0;
    const frameHeaderDescriptionByte = @as(u8, @intCast(dictIDSizeCode | (checksumFlag << 2) | (@as(u32, @intFromBool(singleSegment)) << 5) | (fcsCode << 6)));

    var pos: usize = 0;

    // Magic number
    if (params.format == .zstd1) {
        MEM_writeLE32(op, MAGICNUMBER);
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
fn writeLastEmptyBlock(dst: []u8) !usize {
    if (dst.len < BLOCKHEADERSIZE) {
        return Error.DstSizeTooSmall;
    }

    // Last block + raw block type + 0 size
    const cBlockHeader24: u32 = 1; // bit 0 = last block, bits 1-2 = 0 (raw type)
    MEM_writeLE24(dst.ptr, cBlockHeader24);
    return BLOCKHEADERSIZE;
}

/// Write a literal (raw uncompressed) block
fn writeLiteralBlock(dst: []u8, src: []const u8, isLastBlock: bool) !usize {
    if (dst.len < BLOCKHEADERSIZE + src.len) {
        return Error.DstSizeTooSmall;
    }

    var op = dst.ptr;

    // Block header:
    // - bit 0: lastBlock flag
    // - bits 1-2: blockType (0 for raw)
    // - bits 3-23: blockSize (21-bit)
    const lastBlockBit: u32 = if (isLastBlock) 1 else 0;
    const blockType: u32 = 0; // raw
    const blockSize: u32 = @intCast(src.len);
    const cBlockHeader24: u32 = lastBlockBit | (blockType << 1) | (blockSize << 3);

    MEM_writeLE24(op, cBlockHeader24);
    op += BLOCKHEADERSIZE;

    // Copy data as-is (raw/literal block)
    @memcpy(op[0..src.len], src);
    return BLOCKHEADERSIZE + src.len;
}

/// Encode sequences into a compressed block
/// For now, returns 0 to fall back to raw blocks
/// TODO: Implement proper FSE/Huffman encoding
fn encodeCompressedBlock(dst: []u8, seqStore: *const Sequence.Store, isLastBlock: bool) !usize {
    _ = dst;
    _ = seqStore;
    _ = isLastBlock;

    // For now, always return 0 to fall back to raw blocks
    // This allows the match finder to work while we implement proper sequence encoding
    // Proper implementation would:
    // 1. Build FSE tables for literal lengths, match lengths, offsets
    // 2. Huffman encode literals if beneficial
    // 3. Encode sequences with FSE
    // 4. Build proper ZSTD compressed block format

    return 0; // Signal to use raw block fallback
}

/// Simple block compression (placeholder) - now just a wrapper for literal blocks
fn compressBlock_simple(dst: []u8, src: []const u8) !usize {
    // Write as uncompressed block (not the last block)
    return writeLiteralBlock(dst, src, false);
}

/// Get maximum compressed size
pub fn compressBound(src_size: usize) usize {
    if (src_size >= MAX_INPUT_SIZE) {
        return 0;
    }
    const bound = src_size + (src_size >> 8) + if (src_size < (128 << 10))
        ((128 << 10) - src_size) >> 11
    else
        0;
    return bound;
}

/// Check if result is an error
pub fn isError(result: usize) bool {
    return result > MAX_INPUT_SIZE;
}

/// Get error code from result
pub fn getErrorCode(result: usize) ErrorCode {
    if (!isError(result)) {
        return .no_error;
    }
    // TODO: Implement proper error code mapping
    return .generic;
}

/// Error codes enum
pub const ErrorCode = enum {
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
pub fn getErrorName(result: usize) []const u8 {
    const err_code = getErrorCode(result);
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

// Sequence storage
const Sequence = struct {
    offBase: i32, // offBase == Offset + REP_NUM, or repcode 1,2,3
    litLength: u16,
    mlBase: u16, // mlBase == matchLength - MINMATCH

    const Store = struct {
        sequencesStart: []Sequence,
        sequences: usize, // index to end of sequences
        litStart: []u8,
        lit: usize, // index to end of literals
        llCode: []u8,
        mlCode: []u8,
        ofCode: []u8,
        maxNbSeq: usize,
        maxNbLit: usize,
        allocator: mem.Allocator,

        fn init(allocator: mem.Allocator) Store {
            return Store{
                .sequencesStart = &[_]Sequence{},
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

        fn deinit(self: *Store) void {
            if (self.sequencesStart.len > 0) self.allocator.free(self.sequencesStart);
            if (self.litStart.len > 0) self.allocator.free(self.litStart);
            if (self.llCode.len > 0) self.allocator.free(self.llCode);
            if (self.mlCode.len > 0) self.allocator.free(self.mlCode);
            if (self.ofCode.len > 0) self.allocator.free(self.ofCode);
        }
    };
};

// Window management
const Window = struct {
    nextSrc: [*]const u8, // next block here to continue on current prefix
    base: [*]const u8, // All regular indexes relative to this position
    dictBase: [*]const u8, // extDict indexes relative to this position
    dictLimit: u32, // below that point, need extDict
    lowLimit: u32, // below that point, no more valid data
};

// Match state
const MatchState = struct {
    window: Window,
    loadedDictEnd: u32,
    nextToUpdate: u32,
    hashLog3: u32,
    hashTable: []u32,
    hashTable3: []u32,
    chainTable: []u32,
    cParams: Context.Parameters.Compression,
    allocator: mem.Allocator,

    fn init(allocator: mem.Allocator, cParams: Context.Parameters.Compression) !MatchState {
        const hashTableSize = @as(usize, 1) << @as(u6, @intCast(cParams.hashLog));
        const hashTable3Size = @as(usize, 1) << @as(u6, @intCast(cParams.hashLog3));
        const chainTableSize = @as(usize, 1) << @as(u6, @intCast(cParams.chainLog));

        return MatchState{
            .window = Window{
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

    fn deinit(self: *MatchState) void {
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
const min_buffer_size = std.compress.zstd.default_window_len + std.compress.zstd.block_size_max;

test "basic compression roundtrip" {
    const src = "Hello, World! This is a test string for compression.";
    var dst: [1024]u8 = undefined;
    const decomp_buf = try std.testing.allocator.create([min_buffer_size]u8);
    defer std.testing.allocator.destroy(decomp_buf);
    const clevel = CLEVEL_DEFAULT;

    try testRoundTrip(src, &dst, clevel, decomp_buf);
}

test "compress bound" {
    try std.testing.expect(compressBound(0) == 64);
    try std.testing.expect(compressBound(100) > 100);
    try std.testing.expect(compressBound(MAX_INPUT_SIZE) == 0);
}

test "fuzz compression roundtrip" {
    const ctx = try std.testing.allocator.create(FuzzContext);
    defer std.testing.allocator.destroy(ctx);

    try std.testing.fuzz(ctx, FuzzContext.testOne, .{});
}

pub const FuzzContext = struct {
    src_buf: [4096]u8,
    dst_buf: [min_buffer_size]u8,
    decomp_buf: [min_buffer_size]u8,
    pub fn testOne(self: *@This(), smith: *std.testing.Smith) !void {
        @disableInstrumentation();
        const src_len = smith.valueRangeAtMost(u32, 0, self.src_buf.len);
        const src = self.src_buf[0..@intCast(src_len)];

        var rng = std.Random.DefaultPrng.init(smith.value(u64));
        rng.random().bytes(src);

        const clevel = smith.valueRangeAtMost(i32, 1, 32);
        try testRoundTrip(src, &self.dst_buf, clevel, &self.decomp_buf);
    }
};

fn testRoundTrip(src: []const u8, dst: []u8, clevel: i32, decomp_buf: []u8) !void {
    const compressed_size = try ZSTD_compress(dst, src, clevel);
    try std.testing.expect(compressed_size > 0);
    std.testing.expect(compressed_size <= compressBound(src.len)) catch |err| {
        std.log.err("error {}", .{err});
        std.log.err("expected: <={x}", .{compressBound(src.len)});
        std.log.err("got: {x}", .{compressed_size});
        return err;
    };

    var decomp_input = std.Io.Reader.fixed(dst[0..compressed_size]);
    var decompress: std.compress.zstd.Decompress = .init(&decomp_input, decomp_buf, .{});
    try decompress.reader.fillMore();
    const decompressed = decompress.reader.buffered();
    std.testing.expect(std.mem.eql(u8, decompressed, src)) catch |err| {
        std.log.err("error {}", .{err});
        std.log.err("expected: {x}", .{src});
        std.log.err("got: {x}", .{decompressed});
        return err;
    };
}
