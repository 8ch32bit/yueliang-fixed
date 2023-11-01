--[[
	Modified by 8ch32bit

	I WAS NOT THE ORIGINAL AUTHOR OF THIS PROGRAM! This was originally written by Kein-Hong Man (khman@users.sf.net),
	original creditgoes to him and any other contributers. This program has been improved both performance wise, and syntax wise.
]]

-- Load libraries

local bit32  = bit32 or bit or require('bit');
local string = string;
local math   = math;

local Bor, Band, LShift, RShift, Extract = bit32.bor, bit32.band, bit32.lshift, bit32.rshift, bit32.extract;
local Sub, Byte, Char, Find, Lower, Format, Gmatch = string.sub, string.byte, string.char, string.find, string.lower, string.format, string.gmatch;
local Abs, Min, Log, Pow, Fmod, Floor = math.abs, math.min, math.log, math.pow, math.fmod, math.floor;

-- Other util funtions

local function IsNaN(a)
	return not a == a;
end;

local function GrabByte(x)
	local C = x % 256;
	
	return RShift(x - C, 8), Char(C);
end;

local function Ldexp(mantissa, exponent) -- Equally as fast as lua's builtin (for Lua 5.3+ support)
    return mantissa * (2 ^ exponent);
end;

local function Frexp(x) -- Faster than lua's builtin (for Lua 5.3+ support/optimization)
	if x == 0 then
		return 0, 0;
	end;
		
	local IsNegative = x < 0;
	local New = Abs(x);
	
	local Mantissa, Exponent = 0, 0;

	Exponent = Floor(Log(New, 2)) + 1;
	Mantissa = New / 2 ^ Exponent;
		
	if Abs(Mantissa) >= 1 then
		Mantissa = Mantissa / 2;
	end;
		
	if IsNegative then
	       	return -Mantissa, Exponent;
	end;

	return Mantissa, Exponent;
end;

-- Main code

local Lua = {};

do
	Lua.Z = {}; -- Zio stream module
	Lua.Y = {}; -- Parser module
	Lua.X = {}; -- Lexer module
	Lua.P = {}; -- Instruction module
	Lua.U = {}; -- String dumper module
	Lua.K = {}; -- Main compiler module

	local size_t = 8;

	local EOZ    = "EOZ";
	local Vararg = "...";

	local Z = Lua.Z;
	
	Z.BufferSize = 512;

	local Y = Lua.Y;
	local X = Lua.X;

	X.MaxSrc  = 80;
	X.MaxInt  = 2147483645; -- constants from elsewhere (see above)
	X.LuaQs   = "'%s'";
	X.LuaLStr = 1;

	-- terminal symbols denoted by reserved words: TK_AND to TK_WHILE
	-- other terminal symbols: TK_NAME to TK_EOS
	X.RESERVED = [[
	TK_AND and
	TK_BREAK break
	TK_DO do
	TK_ELSE else
	TK_ELSEIF elseif
	TK_END end
	TK_FALSE false
	TK_FOR for
	TK_FUNCTION function
	TK_IF if
	TK_IN in
	TK_LOCAL local
	TK_NIL nil
	TK_NOT not
	TK_OR or
	TK_REPEAT repeat
	TK_RETURN return
	TK_THEN then
	TK_TRUE true
	TK_UNTIL until
	TK_WHILE while
	TK_CONCAT ..
	TK_DOTS ...
	TK_EQ ==
	TK_GE >=
	TK_LE <=
	TK_NE ~=
	TK_NAME <name>
	TK_NUMBER <number>
	TK_STRING <string>
	TK_EOS <eof>]];

	local P = Lua.P;

	--[[
	===========================================================================
		We assume that instructions are unsigned numbers.
		All instructions have an opcode in the first 6 bits.
		Instructions can have the following fields:
					'A' : 8 bits
					'B' : 9 bits
					'C' : 9 bits
					'Bx' : 18 bits ('B' and 'C' together)
					'sBx' : signed Bx

		A signed argument is represented in excess K; that is, the number
		value is the unsigned value minus K. K is exactly the maximum value
		for that argument (so that -max is represented by 0, and +max is
		represented by 2*max), which is half the maximum for the corresponding
		unsigned argument.
	===========================================================================
	--]]

	P.OpMode = { iABC = 0, iABx = 1, iAsBx = 2 };
	
	P.SIZE_C  = 9;
	P.SIZE_B  = 9;
	P.SIZE_Bx = 18;
	P.SIZE_A  = 8;

	P.SIZE_OP = 6;
	P.POS_OP  = 0;
	
	P.POS_A  = P.POS_OP + P.SIZE_OP;
	P.POS_C  = P.POS_A + P.SIZE_A;
	P.POS_B  = P.POS_C + P.SIZE_C;
	P.POS_Bx = P.POS_C;

	P.MAXARG_Bx  = 262143;
	P.MAXARG_sBx = 131071;

	P.MAXARG_A = 255;
	P.MAXARG_B = 511;
	P.MAXARG_C = 511;
	
	--[[--------------------------------------------------------------------
		Visual representation for reference:

		 31    |    |     |            0      bit position
			+-----+-----+-----+----------+
			|  B  |  C  |  A  |  Opcode  |      iABC format
			+-----+-----+-----+----------+
			-  9  -  9  -  8  -    6     -      field sizes
			+-----+-----+-----+----------+
			|   [s]Bx   |  A  |  Opcode  |      iABx | iAsBx format
			+-----+-----+-----+----------+

	----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	Lua virtual machine opcodes (enum OpCode):
	------------------------------------------------------------------------
	name          args    description
	------------------------------------------------------------------------
	OP_MOVE       A B     R(A) := R(B)
	OP_LOADK      A Bx    R(A) := Kst(Bx)
	OP_LOADBOOL   A B C   R(A) := (Bool)B; if (C) pc++
	OP_LOADNIL    A B     R(A) := ... := R(B) := nil
	OP_GETUPVAL   A B     R(A) := UpValue[B]
	OP_GETGLOBAL  A Bx    R(A) := Gbl[Kst(Bx)]
	OP_GETTABLE   A B C   R(A) := R(B)[RK(C)]
	OP_SETGLOBAL  A Bx    Gbl[Kst(Bx)] := R(A)
	OP_SETUPVAL   A B     UpValue[B] := R(A)
	OP_SETTABLE   A B C   R(A)[RK(B)] := RK(C)
	OP_NEWTABLE   A B C   R(A) := {} (size = B,C)
	OP_SELF       A B C   R(A+1) := R(B); R(A) := R(B)[RK(C)]
	OP_ADD        A B C   R(A) := RK(B) + RK(C)
	OP_SUB        A B C   R(A) := RK(B) - RK(C)
	OP_MUL        A B C   R(A) := RK(B) * RK(C)
	OP_DIV        A B C   R(A) := RK(B) / RK(C)
	OP_MOD        A B C   R(A) := RK(B) % RK(C)
	OP_POW        A B C   R(A) := RK(B) ^ RK(C)
	OP_UNM        A B     R(A) := -R(B)
	OP_NOT        A B     R(A) := not R(B)
	OP_LEN        A B     R(A) := length of R(B)
	OP_CONCAT     A B C   R(A) := R(B).. ... ..R(C)
	OP_JMP        sBx     pc+=sBx
	OP_EQ         A B C   if ((RK(B) == RK(C)) ~= A) then pc++
	OP_LT         A B C   if ((RK(B) <  RK(C)) ~= A) then pc++
	OP_LE         A B C   if ((RK(B) <= RK(C)) ~= A) then pc++
	OP_TEST       A C     if not (R(A) <=> C) then pc++
	OP_TESTSET    A B C   if (R(B) <=> C) then R(A) := R(B) else pc++
	OP_CALL       A B C   R(A), ... ,R(A+C-2) := R(A)(R(A+1), ... ,R(A+B-1))
	OP_TAILCALL   A B C   return R(A)(R(A+1), ... ,R(A+B-1))
	OP_RETURN     A B     return R(A), ... ,R(A+B-2)  (see note)
	OP_FORLOOP    A sBx   R(A)+=R(A+2); if R(A) <?= R(A+1) then { pc+=sBx; R(A+3)=R(A) }
	OP_FORPREP    A sBx   R(A)-=R(A+2); pc+=sBx
	OP_TFORLOOP   A C     R(A+3), ... ,R(A+2+C) := R(A)(R(A+1), R(A+2)); if R(A+3) ~= nil then R(A+2)=R(A+3) else pc++
	OP_SETLIST    A B C   R(A)[(C-1)*FPF+i] := R(A+i), 1 <= i <= B
	OP_CLOSE      A       close all variables in the stack up to (>=) R(A)
	OP_CLOSURE    A Bx    R(A) := closure(KPROTO[Bx], R(A), ... ,R(A+n))
	OP_VARARG     A B     R(A), R(A+1), ..., R(A+B-1) = vararg
	----------------------------------------------------------------------]]

	local OpNames, OpCode, ROpCode = {}, {}, {};
	
	local Amount = 0;
	
	for V in Gmatch([[
	MOVE LOADK LOADBOOL LOADNIL GETUPVAL
	GETGLOBAL GETTABLE SETGLOBAL SETUPVAL SETTABLE
	NEWTABLE SELF ADD SUB MUL
	DIV MOD POW UNM NOT
	LEN CONCAT JMP EQ LT
	LE TEST TESTSET CALL TAILCALL
	RETURN FORLOOP FORPREP TFORLOOP SETLIST
	CLOSE CLOSURE VARARG
	]], "%S+") do
		local Name = "OP_" .. V;
		
		OpCode[Name]    = Amount;
		OpNames[Amount] = V;
		ROpCode[Amount] = Name;
				
		Amount = Amount + 1;
	end;
	
	P.NumOpcodes = Amount;
	P.OpCode     = OpCode;
	P.OpNames    = OpNames;
	P.ROpCode    = ROpCode;

	--[[
	===========================================================================
		Notes:
		(*) In OP_CALL, if (B == 0) then B = top. C is the number of returns - 1,
				and can be 0: OP_CALL then sets 'top' to last_result+1, so
				next open instruction (OP_CALL, OP_RETURN, OP_SETLIST) may use 'top'.
		(*) In OP_VARARG, if (B == 0) then use actual number of varargs and
				set top (like in OP_CALL with C == 0).
		(*) In OP_RETURN, if (B == 0) then return up to 'top'
		(*) In OP_SETLIST, if (B == 0) then B = 'top';
				if (C == 0) then next 'instruction' is real C
		(*) For comparisons, A specifies what condition the test should accept
				(true or false).
		(*) All 'skips' (pc++) assume that next instruction is a jump
	===========================================================================
	--]]

	--[[--------------------------------------------------------------------
		masks for instruction properties. The format is:
		bits 0-1: op mode
		bits 2-3: C arg mode
		bits 4-5: B arg mode
		bit 6: instruction set register A
		bit 7: operator is a test

		for OpArgMask:
		OpArgN - argument is not used
		OpArgU - argument is used
		OpArgR - argument is a register or a jump offset
		OpArgK - argument is a constant or register/constant
	----------------------------------------------------------------------]]

	P.OpArgMask = { OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3 };
	
	P.LFIELDS_PER_FLUSH = 50;
	
	local function Opmode(T, A, B, C, __OpMode)
		local OpArgMask = P.OpArgMask;
		local OpMode    = P.OpMode;
		
		return Bor(Bor(LShift(T, 7), LShift(A, 6)) + Bor(LShift(OpArgMask[b], 4), LShift(OpArgMask[c], 2)), 4 + OpMode[m]);
	end;

	P.OpModes = {
		Opmode(0, 1, "OpArgK", "OpArgN", "iABx"),     -- OP_LOADK
		Opmode(0, 1, "OpArgU", "OpArgU", "iABC"),     -- OP_LOADBOOL
		Opmode(0, 1, "OpArgR", "OpArgN", "iABC"),     -- OP_LOADNIL
		Opmode(0, 1, "OpArgU", "OpArgN", "iABC"),     -- OP_GETUPVAL
		Opmode(0, 1, "OpArgK", "OpArgN", "iABx"),     -- OP_GETGLOBAL
		Opmode(0, 1, "OpArgR", "OpArgK", "iABC"),     -- OP_GETTABLE
		Opmode(0, 0, "OpArgK", "OpArgN", "iABx"),     -- OP_SETGLOBAL
		Opmode(0, 0, "OpArgU", "OpArgN", "iABC"),     -- OP_SETUPVAL
		Opmode(0, 0, "OpArgK", "OpArgK", "iABC"),     -- OP_SETTABLE
		Opmode(0, 1, "OpArgU", "OpArgU", "iABC"),     -- OP_NEWTABLE
		Opmode(0, 1, "OpArgR", "OpArgK", "iABC"),     -- OP_SELF
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_ADD
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_SUB
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_MUL
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_DIV
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_MOD
		Opmode(0, 1, "OpArgK", "OpArgK", "iABC"),     -- OP_POW
		Opmode(0, 1, "OpArgR", "OpArgN", "iABC"),     -- OP_UNM
		Opmode(0, 1, "OpArgR", "OpArgN", "iABC"),     -- OP_NOT
		Opmode(0, 1, "OpArgR", "OpArgN", "iABC"),     -- OP_LEN
		Opmode(0, 1, "OpArgR", "OpArgR", "iABC"),     -- OP_CONCAT
		Opmode(0, 0, "OpArgR", "OpArgN", "iAsBx"),    -- OP_JMP
		Opmode(1, 0, "OpArgK", "OpArgK", "iABC"),     -- OP_EQ
		Opmode(1, 0, "OpArgK", "OpArgK", "iABC"),     -- OP_LT
		Opmode(1, 0, "OpArgK", "OpArgK", "iABC"),     -- OP_LE
		Opmode(1, 1, "OpArgR", "OpArgU", "iABC"),     -- OP_TEST
		Opmode(1, 1, "OpArgR", "OpArgU", "iABC"),     -- OP_TESTSET
		Opmode(0, 1, "OpArgU", "OpArgU", "iABC"),     -- OP_CALL
		Opmode(0, 1, "OpArgU", "OpArgU", "iABC"),     -- OP_TAILCALL
		Opmode(0, 0, "OpArgU", "OpArgN", "iABC"),     -- OP_RETURN
		Opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"),    -- OP_FORLOOP
		Opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"),    -- OP_FORPREP
		Opmode(1, 0, "OpArgN", "OpArgU", "iABC"),     -- OP_TFORLOOP
		Opmode(0, 0, "OpArgU", "OpArgU", "iABC"),     -- OP_SETLIST
		Opmode(0, 0, "OpArgN", "OpArgN", "iABC"),     -- OP_CLOSE
		Opmode(0, 1, "OpArgU", "OpArgN", "iABx"),     -- OP_CLOSURE
		Opmode(0, 1, "OpArgU", "OpArgN", "iABC"),     -- OP_VARARG
	};
	
	P.OpModes[0] = Opmode(0, 1, "OpArgR", "OpArgN", "iABC"); -- OP_MOVE

	------------------------------------------------------------------------
	-- this bit 1 means constant (0 means register)
	------------------------------------------------------------------------
	P.BitRK      = Ldexp(1, P.SizeB - 1);
	P.MaxIndexRK = luaP.BitRK - 1;

	------------------------------------------------------------------------
	-- invalid register that fits in 8 bits
	------------------------------------------------------------------------
	P.NO_REG = P.MAXARG_A;
	
	local U = Lua.U;
	local K = Lua.K;

	------------------------------------------------------------------------
	-- * reader() should return a string, or nil if nothing else to parse.
	--   Additional data can be set only during stream initialization
	-- * Readers are handled in lauxlib.c, see luaL_load(file|buffer|string)
	-- * LUAL_BUFFERSIZE=BUFSIZ=512 in make_getF() (located in luaconf.h)
	-- * Original Reader typedef:
	--   const char * (*lua_Reader) (lua_State *L, void *ud, size_t *sz);
	-- * This Lua chunk reader implementation:
	--   returns string or nil, no arguments to function
	------------------------------------------------------------------------

	------------------------------------------------------------------------
	-- create a chunk reader from a source string
	------------------------------------------------------------------------
	function Z:make_getS(buff)
		return function() -- chunk reader anonymous function here
			if not buff then
				return;
			end;

			local Data = buff;
			buff = nil;

			return Data;
		end;
	end;

	------------------------------------------------------------------------
	-- create a chunk reader from a source file
	------------------------------------------------------------------------
	function Z:make_getF(source)
		local Position = 1;
		local Length   = #source;

		local BuffSize  = self.BufferSize;
		local BuffSize1 = BuffSize - 1;

		return function() -- chunk reader anonymous function here
			local Buff = Sub(source, Position, Position + BuffSize1); -- Use string.sub() instead of :sub()
			Position = Min(Length + 1, Position + BuffSize);

			return Buff;
		end;
	end;

	------------------------------------------------------------------------
	-- creates a zio input stream
	-- returns the ZIO structure, Zio
	------------------------------------------------------------------------
	function Z:init(reader, data)
		if not reader then
			return;
		end;

		return { -- Return zio object
			Reader = reader,
			Data   = Data or "",
			Name   = Name,

			P = 0, N = (not data or data == "") and 0 or #data
		};
	end;

	------------------------------------------------------------------------
	-- fill up input buffer
	------------------------------------------------------------------------
	function Z:fill(zio)
		local Buff = zio.Reader();

		zio.Data = Buff;

		if not Buff or Buff == "" then
			return EOZ;
		end;

		zio.P = 1;
		zio.N = #Buff - 1;

		return Sub(Buff, 1, 1);
	end;

	------------------------------------------------------------------------
	-- get next character from the input stream
	-- * local n, p are used to optimize code generation
	------------------------------------------------------------------------
	function Z:zgetc(zio)
		local N = zio.N;
		local P = zio.P + 1;

		if N > 0 then
			zio.N = N - 1;
			zio.P = P;

			return Sub(zio.Data, P, P);
		end;

		return self:fill(zio);
	end;

	-- FIRST_RESERVED is not required as tokens are manipulated as strings
	-- TOKEN_LEN deleted; maximum length of a reserved word not needed

	-- NUM_RESERVED is not required; number of reserved words

	--[[--------------------------------------------------------------------
	-- Instead of passing seminfo, the Token struct (e.g. ls.t) is passed
	-- so that lexer functions can use its table element, ls.t.seminfo
	--
	-- SemInfo (struct no longer needed, a mixed-type value is used)
	--
	-- Token (struct of ls.t and ls.lookahead):
	--   token  -- token symbol
	--   seminfo  -- semantics information
	--
	-- LexState (struct of ls; ls is initialized by luaX:setinput):
	--   current  -- current character (charint)
	--   linenumber  -- input line counter
	--   lastline  -- line of last token 'consumed'
	--   t  -- current token (table: struct Token)
	--   lookahead  -- look ahead token (table: struct Token)
	--   fs  -- 'FuncState' is private to the parser
	--   L -- LuaState
	--   z  -- input stream
	--   buff  -- buffer for tokens
	--   source  -- current source name
	--   decpoint -- locale decimal point
	--   nestlevel  -- level of nested non-terminals
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- initialize lexer
	-- * original luaX_init has code to create and register token strings
	-- * luaX.tokens: TK_* -> token
	-- * luaX.enums:  token -> TK_* (used in luaX:llex)
	------------------------------------------------------------------------
	function X:init()
		local Tokens, Enums = {}, {};

		local Reserved = self.RESERVED;

		for V in Gmatch(Reserved, "[^\n]+") do
			local _, _, Tok, Str = Find(V, "(%S+)%s+(%S+)");

			Tokens[tok] = Str;
			Enums[str]  = Tok;
		end;

		self.Tokens = Tokens;
		self.Enums  = Enums;
	end;

	------------------------------------------------------------------------
	-- returns a suitably-formatted chunk name or id
	-- * from lobject.c, used in llex.c and ldebug.c
	-- * the result, out, is returned (was first argument)
	------------------------------------------------------------------------
	function X:chunkid(source, buffLength)
		local Output = "";

		local First = Sub(source, 1, 1);

		if First == "=" then
			Output = Sub(source, 2, buffLength);  -- remove first char
		else  -- out = "source", or "...source"
			local Length = #source;

			if First == "@" then
				source = Sub(source, 2);  -- skip the '@'
				
				buffLength = buffLength - 8; -- bufflen = bufflen - #(" '...' ");

				if Length > buffLength then
					source = Sub(source, 1 + (Length - buffLength));  -- get last part of file name
					Output = Output .. Vararg;
				end;

				Output = Output .. source;
			else
				local Len = Find(source, "[\n\r]");  -- stop at first newline

				Len = Len and (Len - 1) or Length;

				buffLength = buffLength - #(" [string \"...\"] ");

				Len = (Len > buffLength) and buffLength or Len;

				Output = "[string \"";

				if Len < Length then  -- must truncate?
					Output = Output .. Sub(source, 1, Len) .. Vararg;
				else
					Output = Output .. source;
				end;

				Output = Output .. "\"]";
			end;
		end;

		return Output;
	end;

	--[[--------------------------------------------------------------------
	-- Support functions for lexer
	-- * all lexer errors eventually reaches lexerror:
			 syntaxerror -> lexerror
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- look up token and return keyword if found (also called by parser)
	------------------------------------------------------------------------
	function X:token2str(_, token)
		if Sub(token, 1, 3) ~= "TK_" then
			if Find(token, "%c") then
				return Format("char(%d)", Byte(token));
			end;

			return token;
		end;

		return self.Tokens[token];
	end;

	function X:textToken(lexState, token)
		if token == "TK_NAME" or token == "TK_STRING" or token == "TK_NUMBER" then
			return lexState.Buff;
		end;

		return self:token2str(nil, token);
	end;

	------------------------------------------------------------------------
	-- throws a lexer error
	-- * txtToken has been made local to luaX:lexerror
	-- * can't communicate LUA_ERRSYNTAX, so it is unimplemented
	------------------------------------------------------------------------
	function X:lexerror(lexState, message, token)
		local Buff    = self:chunkid(lexState.Source, self.MaxSrc);
		local Message = Format("%s:%d: %s", Buff, lexState.LineNumber, message);

		if token then
			Message = Format("%s near " .. self.LuaQs, Message, self:textToken(lexState, token));
		end;
		
		error(Message, 0);
	end;

	------------------------------------------------------------------------
	-- throws a syntax error (mainly called by parser)
	-- * ls.t.token has to be set by the function calling luaX:llex
	--   (see luaX:next and luaX:lookahead elsewhere in this file)
	------------------------------------------------------------------------
	function X:syntaxerror(lexState, message)
		self:lexerror(lexState, message, lexState.T.Token);
	end;

	------------------------------------------------------------------------
	-- move on to next line
	------------------------------------------------------------------------
	function X:currIsNewline(lexState)
		local Current = lexState.Current;

		return Current == "\n" or Current == "\r";
	end;

	function X:inclinenumber(lexState)
		local Old = lexState.Current;
		
		self:nextc(lexState);

		if self:currIsNewline(lexState) and lexState.Current ~= Old then
			self:nextc(ls);
		end;

		lexState.LineNumber = lexState.LineNumber + 1;

		if lexState.LineNumber >= self.MaxInt then
			self:syntaxerror(lexState, "chunk has too many lines");
		end;
	end;

	------------------------------------------------------------------------
	-- initializes an input stream for lexing
	-- * if ls (the lexer state) is passed as a table, then it is filled in,
	--   otherwise it has to be retrieved as a return value
	-- * LUA_MINBUFFER not used; buffer handling not required any more
	------------------------------------------------------------------------
	function X:setinput(luaState, lexState, zio, source) 
		lexState = lexState or {}; -- create struct

		lexState.Lookahead = lexState.Lookahead or {};
		lexState.T         = lexState.T or {};

		lexState.DecPoint = ".";

		lexState.L  = luaState;
		lexState.Z  = zio;
		lexState.Fs = nil;

		lexState.LineNumber = 1;
		lexState.LastLine   = 1;

		lexState.Source = source;

		lexState.Lookahead.Token = "TK_EOS"  -- no look-ahead token

		self:nextc(lexState);  -- read first char
	end;

	--[[--------------------------------------------------------------------
	-- LEXICAL ANALYZER
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- checks if current character read is found in the set 'set'
	------------------------------------------------------------------------
	function X:check_next(lexState, set)
		if Find(set, lexState.Current, 1, 1) then
			self:save_and_next(lexState);

			return true;
		end;

		return false;
	end;

	------------------------------------------------------------------------
	-- retrieve next token, checking the lookahead buffer if necessary
	-- * note that the macro next(ls) in llex.c is now luaX:nextc
	-- * utilized used in lparser.c (various places)
	------------------------------------------------------------------------
	function X:next(lexState)
		lexState.LastLine = lexState.LineNumber;

		local T = lexState.T;

		if lexState.Lookahead.Token ~= "TK_EOS" then  -- is there a look-ahead token?
			local L = lexState.Lookahead;

			T.SemInfo = L.SemInfo;  -- use this one
			T.Token   = L.Token;

			L.Token = "TK_EOS";  -- and discharge it
		else
			T.token = self:llex(lexState, T);  -- read next token
		end
	end

	------------------------------------------------------------------------
	-- fill in the lookahead buffer
	-- * utilized used in lparser.c:constructor
	------------------------------------------------------------------------
	function X:lookahead(ls)
		local Lookahead = lexState.Lookahead;

		Lookahead.Token = self:llex(lexState, Lookahead);
	end;

	------------------------------------------------------------------------
	-- gets the next character and returns it
	-- * this is the next() macro in llex.c; see notes at the beginning
	------------------------------------------------------------------------
	function X:nextc(ls)
		local C = Z:zgetc(lexState.Z);
		lexState.Current = C;

		return C;
	end

	------------------------------------------------------------------------
	-- saves the given character into the token buffer
	-- * buffer handling code removed, not used in this implementation
	-- * test for maximum token buffer length not used, makes things faster
	------------------------------------------------------------------------

	function X:save(lexState, c)
		lexState.Buff = lexState.Buff .. C;
	end

	------------------------------------------------------------------------
	-- save current character into token buffer, grabs next character
	-- * like luaX:nextc, returns the character read for convenience
	------------------------------------------------------------------------
	function X:save_and_next(lexState)
		self:save(lexState, lexState.Current);

		return self:nextc(lexState);
	end

	------------------------------------------------------------------------
	-- LUA_NUMBER
	-- * luaX:read_numeral is the main lexer function to read a number
	-- * luaX:str2d, luaX:buffreplace, luaX:trydecpoint are support functions
	------------------------------------------------------------------------

	------------------------------------------------------------------------
	-- string to number converter (was luaO_str2d from lobject.c)
	-- * returns the number, nil if fails (originally returns a boolean)
	-- * conversion function originally lua_str2number(s,p), a macro which
	--   maps to the strtod() function by default (from luaconf.h)
	------------------------------------------------------------------------
	function X:str2d(str)
		local Result = tonumber(str);

		if Result then
			return Result;
		end;
		
		if Lower(Sub(str, 1, 2)) == "0x" then  -- maybe an hexadecimal constant?
			Result = tonumber(s, 16);

			if Result then
				return Result;
			end;
		end;
	end;

	------------------------------------------------------------------------
	-- single-character replacement, for locale-aware decimal points
	------------------------------------------------------------------------
	function X:buffreplace(lexState, from, to)
		local Result, Buff = "", lexState.Buff;
		local Length = #Buff;

		for Position = 1, Length do
			local C = Sub(buff, Position, Position);

			if C == from then
				C = to;
			end;

			Result = Result .. C;
		end;

		lexState.Buff = Result;
	end

	------------------------------------------------------------------------
	-- Attempt to convert a number by translating '.' decimal points to
	-- the decimal point character used by the current locale. This is not
	-- needed in Yueliang as Lua's tonumber() is already locale-aware.
	-- Instead, the code is here in case the user implements localeconv().
	------------------------------------------------------------------------
	function X:trydecpoint(lexState, token)
		local Old = lexState.decpoint;

		self:buffreplace(lexState, Old, lexState.DecPoint);  -- try updated decimal separator
		local SemInfo = self:str2d(lexState.Buff);

		token.SemInfo = SemInfo;

		if not SemInfo then
			self:buffreplace(lexState, lexState.DecPoint, ".");  -- undo change (for error message)
			self:lexerror(lexState, "malformed number", "TK_NUMBER");
		end
	end

	------------------------------------------------------------------------
	-- main number conversion function
	-- * "^%w$" needed in the scan in order to detect "EOZ"
	------------------------------------------------------------------------
	function X:read_numeral(lexState, token)
		repeat self:save_and_next(lexState); until Find(lexState.Current, "%D") and lexState.Current ~= ".";

		if self:check_next(lexState, "Ee") then  -- 'E'?
			self:check_next(lexState, "+-");  -- optional exponent sign
		end;

		while Find(lexState.Current, "^%w$") or lexState.Current == "_" do
			self:save_and_next(lexState);
		end;

		self:buffreplace(ls, ".", ls.decpoint);  -- follow locale for decimal point
		
		local SemInfo = self:str2d(lexState.Buff);

		token.SemInfo = SemInfo;

		if not SemInfo then  -- format error?
			self:trydecpoint(lexState, token); -- try to update decimal point separator
		end;
	end;

	------------------------------------------------------------------------
	-- count separators ("=") in a long string delimiter
	-- * used by luaX:read_long_string
	------------------------------------------------------------------------
	function X:skip_sep(lexState)
		local Count = 0;
		local Str = lexState.Current;
		
		self:save_and_next(lexState);

		while lexState.Current == "=" do
			self:save_and_next(lexState);

			Count = Count + 1;
		end;

		return (lexState.Current == Str) and Count or (-Count) - 1;
	end;

	------------------------------------------------------------------------
	-- reads a long string or long comment
	------------------------------------------------------------------------
	function X:read_long_string(lexState, token, seperator)
		local Count = 0;

		self:save_and_next(lexState);  -- skip 2nd '['

		if self:currIsNewline(lexState) then  -- string starts with a newline?
			self:inclinenumber(lexState)  -- skip it
		end;

		while true do
			local C = lexState.Current;

			if C == "EOZ" then
				self:lexerror(lexState, token and "unfinished long string" or "unfinished long comment", "TK_EOS");
			elseif C == "[" then
				if self.LuaLStr then
					if self:skip_sep(lexState) == seperator then
						self:save_and_next(lexState);  -- skip 2nd '['

						Count = Count + 1;

						if self.LuaLStr == 1 then
							if seperator == 0 then
								self:lexerror(ls, "nesting of [[...]] is deprecated", "[")
							end;
						end;
					end;
				end;
			elseif C == "]" then
				if self:skip_sep(lexState) == seperator then
					self:save_and_next(lexState);  -- skip 2nd ']'
					
					if self.LuaLStr and self.LuaLStr == 2 then
						Count = Count - 1;

						if seperator == 0 and Count >= 0 then
							break;
						end;
					end;
					
					break;
				end;
			elseif self:currIsNewline(lexState) then
				self:save(lexState, "\n");
				self:inclinenumber(lexState);

				if not token then
					lexState.Buff = "";
				end;
			else
				if token then
					self:save_and_next(lexState);
				else
					self:nextc(lexState);
				end;
			end;
		end;

		if token then
			local P = 3 + seperator;

			token.SemInfo = string.sub(lexState.Buff, P, -P)
		end;
	end;

	------------------------------------------------------------------------
	-- reads a string
	-- * has been restructured significantly compared to the original C code
	------------------------------------------------------------------------

	function X:read_string(lexState, del, token)
		self:save_and_next(lexState);

		while lexState.current ~= del do
			local C = lexState.current;

			if C == "EOZ" then
				self:lexerror(lexState, "unfinished string", "TK_EOS");
			elseif self:currIsNewline(lexState) then
				self:lexerror(lexState, "unfinished string", "TK_STRING");
			end;

			if C == "\\" then
				C = self:nextc(lexState);  -- do not save the '\'

				if self:currIsNewline(lexState) then
					self:save(lexState, "\n");
					self:inclinenumber(lexState);
				elseif C ~= "EOZ" then
					local I = Find("abfnrtv", C, 1, 1);

					if I then
						self:save(lexState, Sub("\a\b\f\n\r\t\v", I, I));
						self:nextc(lexState);
					elseif not Find(C, "%d") then
						self:save_and_next(lexState);  -- handles \\, \", \', and \?
					else  -- \xxx
						C, I = 0, 0;

						repeat
							C = 10 * C + lexState.Current;

							self:nextc(lexState);

							i = i + 1;
						until i >= 3 or not Find(lexState.Current, "%d");

						if C > 255 then  -- UCHAR_MAX
							self:lexerror(lexState, "escape sequence too large", "TK_STRING");
						end;

						self:save(lexState, Char(C));
					end;
				end;
			else
				self:save_and_next(lexState);
			end;
		end;

		self:save_and_next(lexState); -- skip delimiter

		token.SemInfo = Sub(lexState.Buff, 2, -2);
	end;

	------------------------------------------------------------------------
	-- main lexer function
	------------------------------------------------------------------------
	function X:llex(lexState, token)
		lexState.Buff = "";

		local Tokens = self.Tokens;
		local Enums  = self.Enums;

		while true do
			local C = lexState.Current;
			
			if self:currIsNewline(lexState) then
				self:inclinenumber(lexState);
			elseif C == "-" then
				C = self:nextc(lexState);

				if C ~= "-" then
					return "-";
				end;

				local Sep = -1;

				if self:nextc(lexState) == '[' then
					Sep = self:skip_sep(lexState);

					lexState.Buff = "";  -- 'skip_sep' may dirty the buffer
				end;

				if Sep >= 0 then
					self:read_long_string(lexState, nil, Sep); -- long comment

					lexState.Buff = "";
				else -- short comment
					while not self:currIsNewline(lexState) and lexState.Current ~= EOZ do
						self:nextc(lexState);
					end;
				end;
			elseif C == "[" then
				local Sep = self:skip_sep(lexState);

				if Sep >= 0 then
					self:read_long_string(lexState, token, Sep);
					return "TK_STRING"
				elseif Sep == -1 then
					return "[";
				end;

				self:lexerror(lexState, "invalid long string delimiter", "TK_STRING");
			elseif C == "=" then
				C = self:nextc(lexState);

				if C ~= "=" then
					return "=";
				end;

				self:nextc(lexState);
					
				return "TK_EQ";
			elseif C == "<" then
				C = self:nextc(lexState);

				if C ~= "=" then
					return "<";
				end;

				self:nextc(lexState);
					
				return "TK_LE";
			elseif C == ">" then
				C = self:nextc(lexState);

				if C ~= "=" then
					return ">";
				end;

				self:nextc(lexState);
					
				return "TK_GE";
			elseif C == "~" then
				C = self:nextc(lexState);

				if C ~= "=" then
					return "~";
				end;

				self:nextc(lexState);
					
				return "TK_NE";
			elseif C == "\"" or C == "'" then
				self:read_string(lexState, C, token);

				return "TK_STRING";
			elseif C == "." then
				C = self:save_and_next(lexState);

				if self:check_next(lexState, ".") then
					if self:check_next(lexState, ".") then
						return "TK_DOTS";   -- ...
					end;

					return "TK_CONCAT";   -- ..
				end;
				
				if not Find(C, "%d") then
					return ".";
				end;

				self:read_numeral(lexState, token);

				return "TK_NUMBER";
			elseif C == EOZ then
				return "TK_EOS";
			end;

			do  -- default
				if Find(C, "%s") then
					self:nextc(lexState);
				elseif Find(C, "%d") then
					self:read_numeral(lexState, token);

					return "TK_NUMBER";
				end;
				
				if Find(C, "[_%a]") then
					-- identifier or reserved word
					repeat C = self:save_and_next(lexState); until C == EOZ or not Find(C, "[_%w]");

					local Buff = lexState.Buff;

					local Token = Enums[token];

					if Token then
						return Token;
					end;

					Token.SemInfo = Buff;

					return "TK_NAME";
				end;

				self:nextc(lexState);
					
				return C;  -- single-char tokens (+ - / ...)
			end;
		end;
	end;

	function P:GET_OPCODE(instr)
		return ROpCode[instr.OP];
	end;
	
	function P:SET_OPCODE(instr, op)
		instr.OP = OpCode[op];
	end;

	function P:GETARG_A(instr)
		return instr.A;
	end;
	
	function P:SETARG_A(instr, value)
		instr.A = value;
	end;

	function P:GETARG_B(instr)
		return instr.B;
	end;
	
	function P:SETARG_B(instr, value)
		instr.B = value;
	end;

	function P:GETARG_C(instr)
		return instr.C;
	end;
	
	function P:SETARG_C(instr, value)
		instr.C = value;
	end;

	function P:GETARG_Bx(instr)
		return instr.Bx
	end;
	
	function P:SETARG_Bx(instr, value)
		instr.Bx = value;
	end;

	function P:GETARG_sBx(instr)
		return instr.Bx - self.MAXARG_sBx;
	end;
	
	function P:SETARG_sBx(instr, value)
		instr.Bx = value + self.MAXARG_sBx;
	end;

	function P:CREATE_ABC(op, a, b, c)
		return { OP = OpCode[op], A = a, B = b, C = c };
	end;

	function P:CREATE_ABx(op, a, bx)
		return { OP = OpCode[op], A = a, Bx = bx };
	end;

	------------------------------------------------------------------------
	-- create an instruction from a number (for OP_SETLIST)
	------------------------------------------------------------------------
	function P:CREATE_Inst(number)
		local OpCode = number % 64;
		number = RShift(number - OpCode, 6);
		
		local A = number % 256;
		
		return self:CREATE_ABx(OpCode, A, RShift(number - A, 8));
	end;

	------------------------------------------------------------------------
	-- returns a 4-char string little-endian encoded form of an instruction
	------------------------------------------------------------------------
	function P:Instruction(instr)
		local OP, A = instr.OP, instr.A; -- guaranteed to exist
		local B, Bx, C = instr.B, instr.Bx, instr.C; -- can be nil
		
		if Bx then -- change to OP/A/B/C format
			instr.C = (Bx % 512);
			instr.B = (Bx - C) / 512;
		end;
		
		local BaseNumber = A * 64 + OP;

		local Char1 = BaseNumber % 256;
		local Char2 = C * 64  + (BaseNumber - Char1) / 256;
		local Char3 = B * 128 + (BaseNumber - Char2) / 256;
		local Char4 = (BaseNumber - Char3) / 256;
		
		return Char(Char1, Char2, Char3, Char4);
	end;

	------------------------------------------------------------------------
	-- decodes a 4-char little-endian string into an instruction struct
	------------------------------------------------------------------------
	function P:DecodeInst(__string)
		local BaseNumber = Byte(__string, 1);
		
		local OP = BaseNumber % 64;
		local A, B, Bx, C;
		
		A = (Byte(__string, 2) * 4 + (BaseNumber - OP) / 64) % 256; 
		C = (Byte(__string, 3) * 4 + (BaseNumber - A)) / 256;
		B = (Byte(__string, 4) * 2 + (BaseNumber - C)) / 512;

		local Instr = {
			OP = OP,
			A  = A,
			C  = C,
		};
		
		if self.OpMode[tonumber(Sub(OpModes[OP + 1], 7, 7))] ~= "iABC" then
			Instr.Bx = B * 512 + C;
		else
			Instr.B  = B;
		end;
		
		return Instr;
	end;

	-- test whether value is a constant
	function P:IsK(x)
		return x >= self.BitRK;
	end;

	-- gets the index of the constant
	function P:IndexK(x)
		return x - self.BitRK;
	end;

	-- code a constant index as a RK value
	function P:RKAsk(x)
		return x + self.BitRK;
	end;

	------------------------------------------------------------------------
	-- e.g. to compare with symbols, luaP:getOpMode(...) == luaP.OpCode.iABC
	-- * accepts opcode parameter as strings, e.g. "OP_MOVE"
	------------------------------------------------------------------------

	function P:GetOpMode(m)
		return OpModes[OpCode[m]] % 4;
	end;

	function P:GetBMode(m)
		return RShift(OpModes[OpCode[m]], 4) % 4;
	end;

	function P:GetCMode(m)
		return RShift(OpModes[OpCode[m]], 2) % 4;
	end;

	function P:TestAMode(m)
		return RShift(OpModes[OpCode[m]], 6) % 2;
	end;

	function P:TestTMode(m)
		return RShift(OpModes[OpCode[m]], 7);
	end;
	
	function U:MakeSetS()
		return function(__string, buff)  -- chunk writer
			if not __string then
				return 0;
			end;
			
			buff.Data = buff.Data .. __string;
			
			return 1;
		end, { Data = "" };
	end;
	
	function U:MakeSetF(fileName)
		local Buff = {};
		local H = Open(fileName, "wb");
		
		if not H then
			return;
		end;

		Buff.H = H;
		
		return function(__string, buff)  -- chunk writer
			local H = buff.H;
			
			if not H then
				return 0;
			end;
			
			if not __string then
				if H:close() then
					return 0;
				end;
			else
				if H:write(s) then
					return 0;
				end;
			end;
			
			return 1;
		end, Buff;
	end;

	------------------------------------------------------------------------
	-- works like the lobject.h version except that TObject used in these
	-- scripts only has a 'value' field, no 'tt' field (native types used)
	------------------------------------------------------------------------
	function U:Type(object)
		local __type = (typeof ~= nil and typeof or type)(object.value);
		
		local Type = -1;
		
		if __type == "nil" then
			Type = 0;
		elseif __type == "boolean" then
			Type = 1;
		elseif __type == "number" then
			Type = 3;
		elseif __type == "string" then
			Type = 4;
		end;

		return Type;
	end;

	-----------------------------------------------------------------------
	-- converts a IEEE754 double number to an 8-byte little-endian string
	-- * luaU:from_double() and luaU:from_int() are adapted from ChunkBake
	-- * supports +/- Infinity, but not denormals or NaNs
	-----------------------------------------------------------------------
	local Inf = 1 / 0;
	local NaN = 0 / 0;
	
	local DoubleConstant = Ldexp(0.5, 33);
	
	function U:FromDouble(x)
		local Sign = x < 0 and 1 or 0;
		
		if Sign == 1 then
			x = -x;
		end;
		
		local Mantissa, Exponent = Frexp(x);
		
		if x == 0 then -- zero
			Mantissa, Exponent = 0, 0;
		elseif x == Inf then
			Mantissa, Exponent = 0, 2047;
		else
			Mantissa = DoubleConstant * (Mantissa * 2) - 1;
			Exponent = Exponent + 1022;
		end;
		
		local Val, Byte = "", "";
		
		local New = Floor(Mantissa);
		
		for _ = 1, 6 do
			local _, __Byte = GrabByte(New); Val = Val .. __Byte; -- 47:0
		end;
		
		Val, Byte = GrabByte(LShift(Exponent, 4) + New); Val = Val .. Byte; -- 55:48
		Val, Byte = GrabByte(LShift(Sign, 7)     + New); Val = Val .. Byte; -- 63:56
		
		return Val;
	end

	-----------------------------------------------------------------------
	-- converts a number to a little-endian 32-bit integer string
	-- * input value assumed to not overflow, can be signed/unsigned
	-----------------------------------------------------------------------
	function U:FromInt(x)
		local Val = "";

		x = Floor(x);
		x = x < 0 and 4294967296 + x or x;
		
		for _ = 1, 4 do
			v = v .. Char(x % 256);
			x = Floor(RShift(x, 8));
		end;
		
		return Val;
	end

	--[[--------------------------------------------------------------------
	-- Functions to make a binary chunk
	-- * many functions have the size parameter removed, since output is
	--   in the form of a string and some sizes are implicit or hard-coded
	----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	-- struct DumpState:
	--   L  -- lua_State (not used in this script)
	--   writer  -- lua_Writer (chunk writer function)
	--   data  -- void* (chunk writer context or data already written)
	--   strip  -- if true, don't write any debug information
	--   status  -- if non-zero, an error has occured
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- dumps a block of bytes
	-- * lua_unlock(D.L), lua_lock(D.L) unused
	------------------------------------------------------------------------
	function U:DumpBlock(b, D)
		if D.Status == 0 then
			D.Status = D.Write(b, D.Data);
		end;
	end;

	------------------------------------------------------------------------
	-- dumps a char
	------------------------------------------------------------------------
	function U:DumpChar(char, D)
		self:DumpBlock(Char(char), D);
	end;

	------------------------------------------------------------------------
	-- dumps a 32-bit signed or unsigned integer (for int) (hard-coded)
	------------------------------------------------------------------------
	function U:DumpInt(x, D)
		self:DumpBlock(self:FromInt(x), D);
	end;

	------------------------------------------------------------------------
	-- dumps a 32-bit signed or unsigned integer (for int) (hard-coded)
	------------------------------------------------------------------------
	function U:DumpSizeT(x, D)
		self:DumpBlock(self:FromInt(x), D);
		
		if size_size_t == 8 then
			self:DumpBlock(self:FromInt(0), D);
		end;
	end;

	------------------------------------------------------------------------
	-- dumps a lua_Number (hard-coded as a double)
	------------------------------------------------------------------------
	function U:DumpNumber(x, D)
		self:DumpBlock(self:FromDouble(x), D);
	end;

	------------------------------------------------------------------------
	-- dumps a Lua string (size type is hard-coded)
	------------------------------------------------------------------------
	function U:DumpString(__string, D)
		if not __string then
			return self:DumpSizeT(0, D);
		end;

		__string = __string .. "\0";
		
		self:DumpSizeT(#__string, D);
		self:DumpBlock(__string, D);
	end;

	------------------------------------------------------------------------
	-- dumps instruction block from function prototype
	------------------------------------------------------------------------
	function U:DumpCode(instr, D)
		local Size = instr.SizeCode;
		
		self:DumpInt(Size, D);
		
		for Index = 0, Size - 1 do
			self:DumpBlock(P:Instruction(Instr.Code[Index]), D);
		end;
	end;

	------------------------------------------------------------------------
	-- dump constant pool from function prototype
	-- * bvalue(o), nvalue(o) and rawtsvalue(o) macros removed
	------------------------------------------------------------------------
	function U:DumpConstants(const, D)
		local Source = const.Source;
		local Size   = const.SizeConst;

		local K, P = const.K, const.P;
			
		self:DumpInt(Size, D);

		local LUA_TBOOLEAN = self.LUA_TBOOLEAN;
		local LUA_TNUMBER  = self.LUA_TNUMBER;
		local LUA_TSTRING  = self.LUA_TSTRING;
		
		for Index = 0, Size - 1 do
			local Object = K[i];
			local Value  = Object.Value;
			local Type   = self:Type(Object);
			
			self:DumpChar(Type, D);
			
			if Type == LUA_TBOOLEAN then
				self:DumpChar(Value and 1 or 0, D);
			elseif Type == LUA_TNUMBER then
				self:DumpNumber(Value, D);
			elseif Type == LUA_TSTRING then
				self:DumpString(Value, D);
			end;
		end;
		
		Size = const.SizeP;
		
		self:DumpInt(Size, D);
		
		for Index = 0, Size - 1 do
			self:DumpFunction(P[Index], Source, D);
		end;
	end;

	------------------------------------------------------------------------
	-- dump debug information
	------------------------------------------------------------------------
	function U:DumpDebug(debug, D)
		local Size     = D.Strip and 0 or debug.SizeLineInfo; -- dump line information
		local LineInfo = debug.LineInfo;
		local LocVars  = debug.LocVars;
		local Upvalues = debug.Upvalues;
		
		self:DumpInt(Size, D);
		
		for Index = 0, Size - 1 do
			self:DumpInt(LineInfo[Index], D);
		end;
		
		Size = D.Strip and 0 or debug.SizeLocalVars;            -- dump local information
		
		self:DumpInt(Size, D);
		
		for Index = 0, Size - 1 do
			local Var = LocVars[Index];
			
			self:DumpString(Var.VarName, D);
			self:DumpInt(Var.StartPC, D);
			self:DumpInt(Var.EndPC, D);
		end;
		
		Size = D.Strip and 0 or f.SizeUpvalues; -- dump upvalue information
		
		self:DumpInt(Size, D);
		
		for Index = 0, Size - 1 do
			self:DumpString(Upvalues[i], D);
		end;
	end;

	------------------------------------------------------------------------
	-- dump child function prototypes from function prototype
	------------------------------------------------------------------------
	function U:DumpFunction(__function, P, D)
		local Source = __function.Source;
		
		if Source == P or D.Strip then
			Source = nil;
		end;
		
		self:DumpString(source, D);
		self:DumpInt(__function.lineDefined, D);
		self:DumpInt(__function.lastlinedefined, D);
		self:DumpChar(__function.nups, D);
		self:DumpChar(__function.numparams, D);
		self:DumpChar(__function.is_vararg, D);
		self:DumpChar(__function.maxstacksize, D);
		self:DumpCode(__function, D);
		self:DumpConstants(__function, D);
		self:DumpDebug(__function, D);
	end

	------------------------------------------------------------------------
	-- dump Lua header section (some sizes hard-coded)
	------------------------------------------------------------------------
	function U:DumpHeader(D)
		local Header = "\27Lua" .. Char(81, 0, 1, 4, size_size_t, 4, 8, 0);
		
		assert(#Header == 12) -- fixed buffer now an assert
		self:DumpBlock(Header, D);
	end;

	------------------------------------------------------------------------
	-- make header (from lundump.c)
	-- returns the header string
	------------------------------------------------------------------------
	function U:Header()
		return "\27Lua" .. Char(81, 0, 1, 4, size_size_t, 4, 8, 0);
	end;

	------------------------------------------------------------------------
	-- dump Lua function as precompiled chunk
	-- (lua_State* L, const Proto* f, lua_Writer w, void* data, int strip)
	-- * w, data are created from make_setS, make_setF
	------------------------------------------------------------------------
	function U:Dump(L, __function, writer, data, strip)
		local D = {};  -- DumpState
		D.L = L;
		D.write = writer;
		D.data  = data;
		D.strip = strip;
		D.status = 0;
		
		self:DumpHeader(D);
		self:DumpFunction(__function, nil, D);
		
		D.write(nil, data);
		
		return D.status;
	end;

	------------------------------------------------------------------------
	-- constants used by code generator
	------------------------------------------------------------------------
	-- maximum stack for a Lua function
	K.MAXSTACK = 250  -- (from llimits.h)

	--[[--------------------------------------------------------------------
	-- other functions
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- emulation of TValue macros (these are from lobject.h)
	-- * TValue is a table since lcode passes references around
	-- * tt member field removed, using Lua's type() instead
	-- * for setsvalue, sethvalue, parameter L (deleted here) in lobject.h
	--   is used in an assert for testing, see checkliveness(g,obj)
	------------------------------------------------------------------------
	function K.IsNumber(object)
		return type(object.Value) == "number"; -- Much more simple
	end;
	
	function K.ObjValue(object)
		return object.Value;
	end;
	
	function K.Set(object, x)
		object.Value = x;
	end;

	function K.SetNil(object)
		object.Value = nil;
	end;
	
	K.SetNValue = K.SetValue;
	K.SetHValue = K.SetValue;
	K.SetBValue = K.SetValue;

	------------------------------------------------------------------------
	-- The luai_num* macros define the primitive operations over numbers.
	-- * this is not the entire set of primitive operations from luaconf.h
	-- * used in luaK:constfolding()
	------------------------------------------------------------------------
	function K.AddNum(a, b)
		return a + b;
	end;
	
	function K.SubNum(a, b)
		return a - b;
	end;
	
	function K.MulNum(a, b)
		return a * b;
	end;
	
	function K.DivNum(a, b)
		return a / b;
	end;
	
	K.ModNum = Fmod; -- function K.NumMod(a, b) return a % b; end;
	K.PowNum = Pow;  -- function K.PowNum(a, b) return a ^ b; end;
	
	function K.UnaryMinus(x)
		return -x;
	end;

	--[[--------------------------------------------------------------------
	-- code generator functions
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- Marks the end of a patch list. It is an invalid value both as an absolute
	-- address, and as a list link (would link an element to itself).
	------------------------------------------------------------------------
	K.NO_JUMP = -1;

	------------------------------------------------------------------------
	-- grep "ORDER OPR" if you change these enums
	------------------------------------------------------------------------
	K.BinOpr = {
		OPR_ADD = 0, OPR_SUB = 1, OPR_MUL = 2, OPR_DIV = 3, OPR_MOD = 4, OPR_POW = 5,
		OPR_CONCAT = 6,
		OPR_NE = 7, OPR_EQ = 8,
		OPR_LT = 9, OPR_LE = 10, OPR_GT = 11, OPR_GE = 12,
		OPR_AND = 13, OPR_OR = 14,
		OPR_NOBINOPR = 15,
	};

	-- * UnOpr is used by luaK:prefix's op argument, but not directly used
	--   because the function receives the symbols as strings, e.g. "OPR_NOT"
	K.UnOpr = {
		OPR_MINUS = 0, OPR_NOT = 1, OPR_LEN = 2, OPR_NOUNOPR = 3,
	};

	------------------------------------------------------------------------
	-- returns the instruction object for given e (expdesc), was a macro
	------------------------------------------------------------------------
	function K.GetCode(fs, e)
		return fs.F.Code[e.Info];
	end;

	------------------------------------------------------------------------
	-- codes an instruction with a signed Bx (sBx) field, was a macro
	-- * used in luaK:jump(), (lparser) luaY:forbody()
	------------------------------------------------------------------------
	local MaxArg_sBx = P.MAXARG_sBx;
	
	function K:CodeAsBx(fs, o, A, sBx)
		return self:CodeABx(fs, o, A, sBx + MaxArg_sBx);
	end;

	------------------------------------------------------------------------
	-- set the expdesc e instruction for multiple returns, was a macro
	------------------------------------------------------------------------
	local MultRet = Y.LUA_MULTRET;
	
	function K:SetMulteReturns(fs, e)
		self:SetReturns(fs, e, MultRet);
	end;

	------------------------------------------------------------------------
	-- there is a jump if patch lists are not identical, was a macro
	-- * used in luaK:exp2reg(), luaK:exp2anyreg(), luaK:exp2val()
	------------------------------------------------------------------------
	function K:HasJumps(e)
		return e.t ~= e.f;
	end

	------------------------------------------------------------------------
	-- true if the expression is a constant number (for constant folding)
	-- * used in constfolding(), infix()
	------------------------------------------------------------------------
	function luaK:IsNumeral(e)
		return e.k == "VKNUM" and e.t == self.NO_JUMP and e.f == self.NO_JUMP
	end

	------------------------------------------------------------------------
	-- codes loading of nil, optimization done if consecutive locations
	-- * used in luaK:discharge2reg(), (lparser) luaY:adjust_assign()
	------------------------------------------------------------------------
	function K:Nil(fs, from, n)
		local PC          = fs.PC;
		local LastTarget  = fs.LastTarget;
		local NactVar     = fs.NactVar;
		local __function  = fs.__function;

		local Code = __function.Code;
		
		if PC > LastTarget then  -- no jumps to current position?
			if PC == 0 then  -- function start?
				if from >= NactVar then
					return;  -- positions are already clean
				end;
			end

			local previous = Code[PC - 1];
			
			if P:GET_OPCODE(previous) == "OP_LOADNIL" then
				local A = P:GETARG_A(previous);
				local B = P:GETARG_B(previous);
				
				if A <= from and from <= B + 1 then  -- can connect both?
					if from + n - 1 > B then
						P:SETARG_B(previous, from + n - 1);
					end;
					
					return;
				end;
			end;
		end;
		
		self:codeABC(fs, "OP_LOADNIL", from, from + n - 1, 0);  -- else no optimization
	end

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:Jump(fs)
		local JPC = fs.JPC;  -- save list of jumps to here
		fs.JPC = -1;
		
		local Instr = self:CodeAsBx(fs, "OP_JMP", 0, -1);
		
		Instr = self:Concat(fs, Instr, JPC);
		
		return Instr;
	end;

	------------------------------------------------------------------------
	-- codes a RETURN instruction
	-- * used in luaY:close_func(), luaY:retstat()
	------------------------------------------------------------------------
	function K:Return(fs, first, nret)
		self:CodeABC(fs, "OP_RETURN", first, nret + 1, 0);
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:jumponcond(), luaK:codecomp()
	------------------------------------------------------------------------
	function K:ConditionalJump(fs, ...)
		self:CodeABC(fs, ...);
		
		return self:Jump(fs);
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:patchlistaux(), luaK:concat()
	------------------------------------------------------------------------
	function K:FixJump(fs, pc, destination)
		local __function = fs.__function;
		local Code       = __function.Code;
		
		local JMP    = Code[pc];
		local Offset = destination - (pc + 1);
		
		if math.abs(Offset) > MaxArg_sBx then
			X:SyntaxError(fs.LexState, "control structure too long");
		end;
		
		P:SETARG_sBx(JMP, Offset);
	end;

	------------------------------------------------------------------------
	-- returns current 'pc' and marks it as a jump target (to avoid wrong
	-- optimizations with consecutive instructions not in the same basic block).
	-- * used in multiple locations
	-- * fs.lasttarget tested only by luaK:_nil() when optimizing OP_LOADNIL
	------------------------------------------------------------------------
	function K:GetLabel(fs)
		local PC = fs.PC;
		fs.LastTarget = PC;
		
		return PC;
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:need_value(), luaK:removevalues(), luaK:patchlistaux(),
	--   luaK:concat()
	------------------------------------------------------------------------
	function K:GetJump(fs, pc)
		local Code = fs.__function.Code;
		
		local Offset = P:GETARG_sBx(Code[pc]);
		
		if Offset == -1 then  -- point to itself represents end of list
			return -1;  -- end of list
		else
			return (pc + 1) + offset;  -- turn offset into absolute position
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:need_value(), luaK:patchtestreg(), luaK:invertjump()
	------------------------------------------------------------------------
	function K:GetJumpControl(fs, pc)
		local Code = fs.__function.Code;
		
		local InstrA = Code[pc];
		local InstrB = Code[pc - 1];
		
		if pc >= 1 and P:TestTMode(P:GET_OPCODE(InstrA)) ~= 0 then
			return InstrA;
		end;

		return InstrB;
	end;

	------------------------------------------------------------------------
	-- check whether list has any jump that do not produce a value
	-- (or produce an inverted value)
	-- * return value changed to boolean
	-- * used only in luaK:exp2reg()
	------------------------------------------------------------------------
	function K:NeedValue(fs, list)
		while list ~= -1 do
			local JMPCtrl = self:GetJumpControl(fs, list);
			
			if P:GET_OPCODE(JMPCtrl) ~= "OP_TESTSET" then
				return true;
			end;
			
			list = self:GetJump(fs, list);
		end;
		
		return false;
	end;

	local NO_REG = P.NO_REG;

	------------------------------------------------------------------------
	--
	-- * used in luaK:removevalues(), luaK:patchlistaux()
	------------------------------------------------------------------------
	function K:PatchTestReg(fs, node, reg)
		local JMPCtrl = self:GetJumpControl(fs, node);
		
		if P:GET_OPCODE(JMPCtrl) ~= "OP_TESTSET" then
			return false;  -- cannot patch other instructions
		end;
		
		if reg ~= NO_REG and reg ~= P:GETARG_B(JMPCtrl) then
			P:SETARG_A(JMPCtrl, reg);
		else
			P:SET_OPCODE(JMPCtrl, "OP_TEST");
			
			local B = P:GETARG_B(JMPCtrl);
			
			P:SETARG_A(i, b);
			P:SETARG_B(i, 0);
		end;
		
		return true;
	end
	
	function K:RemoveValues(fs, list)
		while list ~= -1 do
			self:PatchTestReg(fs, list, NO_REG);
			list = self:GetJump(fs, list);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:dischargejpc(), luaK:patchlist(), luaK:exp2reg()
	------------------------------------------------------------------------
	function K:PatchListAux(fs, list, vTarget, reg, dTarget)
		while list ~= -1 do
			local Next = self:GetJump(fs, list);
			
			if self:PatchTestReg(fs, list, reg) then
				self:FixJump(fs, list, vTarget);
			else
				self:FixJump(fs, list, dTarget);  -- jump to default target
			end;
			
			list = Next;
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used only in luaK:code()
	------------------------------------------------------------------------
	function K:DischargeJPC(fs)
		local PC, JPC = fs.PC, fs.JPC;
		
		self:patchlistaux(fs, JPC, PC, NO_REG, PC);
		
		fs.JPC = -1;
	end;

	------------------------------------------------------------------------
	--
	-- * used in (lparser) luaY:whilestat(), luaY:repeatstat(), luaY:forbody()
	------------------------------------------------------------------------
	function K:PatchList(fs, list, target)
		if target == fs.PC then
			self:PatchToHere(fs, list);
		else
			self:patchlistaux(fs, list, target, NO_REG, target);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:PatchToHere(fs, list)
		self:GetLabel(fs);
		
		fs.jpc = self:Concat(fs, fs.jpc, list);
	end

	------------------------------------------------------------------------
	-- * l1 was a pointer, now l1 is returned and callee assigns the value
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:Concat(fs, list1, list2)
		if list2 == -1 then
			return list1;
		elseif list1 == -1 then
			return list2;
		else
			local List = list1;
			local Next = self:GetJump(fs, List);
			
			while Next ~= -1 do  -- find last element
				List = Next;
				Next = self:GetJump(fs, list);
			end;
			
			self:FixJump(fs, list, l2);
		end;
		
		return list1;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:reserveregs(), (lparser) luaY:forlist()
	------------------------------------------------------------------------
	local MaxStack = K.MAXSTACK or 250;
	
	function K:CheckStack(fs, n)
		local NewStack   = fs.FreeReg + n;
		local __function = fs.__function;
		
		if NewStack > __function.MaxStackSize then
			if NewStack >= MaxStack then
				luaX:SyntaxError(fs.ls, "function or expression too complex")
			end;
			
			__function.MaxStackSize = NewStack;
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:ReserveRegs(fs, n)
		self:CheckStack(fs, n);
		
		fs.FreeReg = fs.FreeReg + n;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:freeexp(), luaK:dischargevars()
	------------------------------------------------------------------------
	function K:FreeReg(fs, reg)
		if not P:ISK(reg) and reg >= fs.NactVar then
			fs.FreeReg = fs.FreeReg - 1;
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:FreeExp(fs, e)
		if e.k == "VNONRELOC" then
			self:FreeReg(fs, e.info);
		end;
	end;

	------------------------------------------------------------------------
	-- * TODO NOTE implementation is not 100% correct, since the assert fails
	-- * luaH_set, setobj deleted; direct table access used instead
	-- * used in luaK:stringK(), luaK:numberK(), luaK:boolK(), luaK:nilK()
	------------------------------------------------------------------------
	function K:AddK(fs, k, v)
		local Value = k.Value;
		
		local L  = fs.L;
		local H  = fs.H;
		local K  = fs.K;
		local NK = fs.NK;
		
		local SizeK      = fs.SizeK;
		local __function = fs.__function;
		
		local Idx = H[Value];
		
		if self:IsNumber(Idx) then
			return self:NValue(Idx);
		end;

		Idx = {}; self:SetNValue(Idx, NK);
			
		H[Value] = Idx;
			
		Y:GrowVector(L, K, NK, SizeK, nil, luaP.MAXARG_Bx, "constant table overflow");
			
		K[NK] = v;
			
		fs.NK = NK + 1;
			
		return NK;
	end;

	------------------------------------------------------------------------
	-- creates and sets a string object
	-- * used in (lparser) luaY:codestring(), luaY:singlevar()
	------------------------------------------------------------------------
	function K:StringK(fs, __string)
		local Object = {};
		self:SetSValue(Object, __string);
		
		return self:AddK(fs, Object, Object);
	end;

	------------------------------------------------------------------------
	-- creates and sets a number object
	-- * used in luaK:prefix() for negative (or negation of) numbers
	-- * used in (lparser) luaY:simpleexp(), luaY:fornum()
	------------------------------------------------------------------------
	function K:NumberK(fs, number)
		local Object = {};
		self:SetNValue(Object, number);
		
		return self:AddK(fs, Object, Object);
	end;

	------------------------------------------------------------------------
	-- creates and sets a boolean object
	-- * used only in luaK:exp2RK()
	------------------------------------------------------------------------
	function K:BoolK(fs, boolean)
		local Object = {};
		self:SetBValue(Object, boolean);
		
		return self:AddK(fs, Object, Object);
	end;

	------------------------------------------------------------------------
	-- creates and sets a nil object
	-- * used only in luaK:exp2RK()
	------------------------------------------------------------------------
	function K:NilK(fs)
		local k, v = {}, {};
		
		self:SetNilValue(v)
		self:SetHValue(k, fs.h);
		
		return self:AddK(fs, k, v);
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:setmultret(), (lparser) luaY:adjust_assign()
	------------------------------------------------------------------------
	function luaK:SetReturns(fs, e, nResults)
		local K, Offset = e.K, nResults + 1;
		local Code      = self:GetCode(fs, e);
		
		if K == "VCALL" then  -- expression is an open function call?
			P:SETARG_C(Code, Offset);
		elseif K == "VVARARG" then
			P:SETARG_B(Code, Offset);
			P:SETARG_A(Code, fs.freereg);
			
			self:ReserveRegs(fs, 1);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:dischargevars(), (lparser) luaY:assignment()
	------------------------------------------------------------------------
	function K:SetOneRet(fs, e)
		local K    = e.K;
		local Code = self:GetCode(fs, e);
		
		if K == "VCALL" then  -- expression is an open function call?
			e.K    = "VNONRELOC";
			e.Info = P:GETARG_A(Code);
		elseif e.k == "VVARARG" then
			e.K = "VRELOCABLE"  -- can relocate its simple result
			P:SETARG_B(Code, 2);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:DischargeVars(fs, e)
		local K    = e.K;
		local Aux  = e.Aux;
		local Info = e.Info;
		
		if K == "VLOCAL" then
			e.K = "VNONRELOC"
		elseif K == "VUPVAL" then
			e.k = "VRELOCABLE";
			e.Info = self:codeABC(fs, "OP_GETUPVAL", 0, Info, 0);
		elseif k == "VGLOBAL" then
			e.k = "VRELOCABLE";
			e.info = self:codeABx(fs, "OP_GETGLOBAL", 0, Info);
		elseif k == "VINDEXED" then
			e.K = "VRELOCABLE";
			
			self:FreeReg(fs, Aux);
			self:FreeReg(fs, Info);
			
			e.Info = self:codeABC(fs, "OP_GETTABLE", 0, Info, Aux);
		elseif k == "VVARARG" or k == "VCALL" then
			self:SetOneRet(fs, e);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used only in luaK:exp2reg()
	------------------------------------------------------------------------
	function K:CodeLabel(fs, a, b, jump)
		self:GetLabel(fs);
		
		return self:CodeABC(fs, "OP_LOADBOOL", a, b, jump);
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:discharge2anyreg(), luaK:exp2reg()
	------------------------------------------------------------------------
	function K:Discharge2Reg(fs, e, reg)
		self:dischargevars(fs, e);
		
		local K    = e.K;
		local Info = e.Info;
		
		
		if K == "VNIL" then
			self:Nil(fs, reg, 1)
		elseif K == "VFALSE" or K == "VTRUE" then
			self:codeABC(fs, "OP_LOADBOOL", reg, (K == "VTRUE") and 1 or 0, 0);
		elseif K == "VK" then
			self:codeABx(fs, "OP_LOADK", reg, Info);
		elseif K == "VKNUM" then
			self:codeABx(fs, "OP_LOADK", reg, self:NumberK(fs, e.NVal));
		elseif K == "VRELOCABLE" then
			local PC = self:GetCode(fs, e);
			
			luaP:SETARG_A(PC, reg);
		elseif K == "VNONRELOC" then
			if reg ~= Info then self:CodeABC(fs, "OP_MOVE", reg, Info, 0); end;
		else
			return assert(e.k == "VVOID" or e.k == "VJMP");
		end;
		
		e.Info = reg;
		e.K = "VNONRELOC";
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:jumponcond(), luaK:codenot()
	------------------------------------------------------------------------
	function K:Discharge2AnyReg(fs, e)
		if e.K ~= "VNONRELOC" then
			self:ReserveRegs(fs, 1);
			self:Discharge2Reg(fs, e, fs.FreeReg - 1);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in luaK:exp2nextreg(), luaK:exp2anyreg(), luaK:storevar()
	------------------------------------------------------------------------
	function K:Exp2Reg(fs, e, reg)
		self:Discharge2Reg(fs, e, reg);

		local T = e.T;
		local K = e.K;
		local F = e.F;
		
		if e.K == "VJMP" then
			e.T = self:Concat(fs, e.T, e.Info); T = e.T;
		end;
		
		if self:hasjumps(e) then
			local final;  -- position after whole expression
			local p_f = -1;  -- position of an eventual LOAD false
			local p_t = -1;  -- position of an eventual LOAD true
			
			if self:NeedValue(fs, T) or self:NeedValue(fs, F) then
				local fj = (K == "VJMP") and -1 or self:Jump(fs);
				
				p_f = self:CodeLabel(fs, reg, 0, 1);
				p_t = self:CodeLabel(fs, reg, 1, 0);
				
				self:PatchToHere(fs, fj);
			end;
			
			final = self:GetLabel(fs);
			
			self:PatchListAux(fs, F, final, reg, p_f);
			self:PatchListAux(fs, T, final, reg, p_t);
		end;
		
		e.F, e.T = -1, -1;
		
		e.Info = reg;
		e.K    = "VNONRELOC";
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:Exp2NextReg(fs, e)
		self:DischargeVars(fs, e);
		self:FreeExp(fs, e);
		self:ReserveRegs(fs, 1);
		self:Exp2Reg(fs, e, fs.FreeReg - 1);
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	function K:Exp2AnyReg(fs, e)
		self:DischargeVars(fs, e);

		local Info = e.Info;
		
		if e.K == "VNONRELOC" then
			if not self:HasJumps(e) then  -- exp is already in a register
				return Info;
			end;
			
			if Info >= fs.nactvar then
				self:Exp2Reg(fs, e, Info);
				
				return Info;
			end;
		end;
		
		self:Exp2NextReg(fs, e);
		
		return Info;
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:exp2RK(), luaK:prefix(), luaK:posfix()
	-- * used in (lparser) luaY:yindex()
	------------------------------------------------------------------------
	function K:Exp2Val(fs, e)
		if self:HasJumps(e) then
			self:Exp2AnyReg(fs, e);
		else
			self:DischargeVars(fs, e);
		end;
	end;

	------------------------------------------------------------------------
	--
	-- * used in multiple locations
	------------------------------------------------------------------------
	local MaxIndexRK = P.MAXINDEXRK;
	
	function K:Exp2RK(fs, e)
		self:Exp2Val(fs, e);
		
		local K    = e.K;
		local Info = e.Info;
		
		if K == "VKNUM" or K == "VTRUE" or K == "VFALSE" or K == "VNIL" then
			if fs.nk <= MaxIndexRK then
				if K == "VNIL" then
					e.Info = self:NilK(fs);
				else
					e.Info = (K == "VKNUM") and self:NumberK(fs, e.NVal) or self:boolK(fs, K == "VTRUE");
				end;
				
				e.K = "VK";
				
				return P:RKAsk(e.Info);
			end;
		elseif K == "VK" then
			if Info <= MaxIndexRK then  -- constant fit in argC?
				return P:RKAsk(Info);
			end
		end;
		
		return self:Exp2AnyReg(fs, e);
	end;

	------------------------------------------------------------------------
	--
	-- * used in (lparser) luaY:assignment(), luaY:localfunc(), luaY:funcstat()
	------------------------------------------------------------------------
	function luaK:storevar(fs, var, ex)
		local k = var.k
		if k == "VLOCAL" then
			self:freeexp(fs, ex)
			self:exp2reg(fs, ex, var.info)
			return
		elseif k == "VUPVAL" then
			local e = self:exp2anyreg(fs, ex)
			self:codeABC(fs, "OP_SETUPVAL", e, var.info, 0)
		elseif k == "VGLOBAL" then
			local e = self:exp2anyreg(fs, ex)
			self:codeABx(fs, "OP_SETGLOBAL", e, var.info)
		elseif k == "VINDEXED" then
			local e = self:exp2RK(fs, ex)
			self:codeABC(fs, "OP_SETTABLE", var.info, var.aux, e)
		else
			lua_assert(0)  -- invalid var kind to store
		end
		self:freeexp(fs, ex)
	end

	------------------------------------------------------------------------
	--
	-- * used only in (lparser) luaY:primaryexp()
	------------------------------------------------------------------------
	function luaK:_self(fs, e, key)
		self:exp2anyreg(fs, e)
		self:freeexp(fs, e)
		local func = fs.freereg
		self:reserveregs(fs, 2)
		self:codeABC(fs, "OP_SELF", func, e.info, self:exp2RK(fs, key))
		self:freeexp(fs, key)
		e.info = func
		e.k = "VNONRELOC"
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:goiftrue(), luaK:codenot()
	------------------------------------------------------------------------
	function luaK:invertjump(fs, e)
		local pc = self:getjumpcontrol(fs, e.info)
		lua_assert(luaP:testTMode(luaP:GET_OPCODE(pc)) ~= 0 and
							 luaP:GET_OPCODE(pc) ~= "OP_TESTSET" and
							 luaP:GET_OPCODE(pc) ~= "OP_TEST")
		luaP:SETARG_A(pc, (luaP:GETARG_A(pc) == 0) and 1 or 0)
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:goiftrue(), luaK:goiffalse()
	------------------------------------------------------------------------
	function luaK:jumponcond(fs, e, cond)
		if e.k == "VRELOCABLE" then
			local ie = self:getcode(fs, e)
			if luaP:GET_OPCODE(ie) == "OP_NOT" then
				fs.pc = fs.pc - 1  -- remove previous OP_NOT
				return self:condjump(fs, "OP_TEST", luaP:GETARG_B(ie), 0, cond and 0 or 1)
			end
			-- else go through
		end
		self:discharge2anyreg(fs, e)
		self:freeexp(fs, e)
		return self:condjump(fs, "OP_TESTSET", luaP.NO_REG, e.info, cond and 1 or 0)
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:infix(), (lparser) luaY:cond()
	------------------------------------------------------------------------
	function luaK:goiftrue(fs, e)
		local pc  -- pc of last jump
		self:dischargevars(fs, e)
		local k = e.k
		if k == "VK" or k == "VKNUM" or k == "VTRUE" then
			pc = self.NO_JUMP  -- always true; do nothing
		elseif k == "VFALSE" then
			pc = self:jump(fs)  -- always jump
		elseif k == "VJMP" then
			self:invertjump(fs, e)
			pc = e.info
		else
			pc = self:jumponcond(fs, e, false)
		end
		e.f = self:concat(fs, e.f, pc)  -- insert last jump in `f' list
		self:patchtohere(fs, e.t)
		e.t = self.NO_JUMP
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:infix()
	------------------------------------------------------------------------
	function luaK:goiffalse(fs, e)
		local pc  -- pc of last jump
		self:dischargevars(fs, e)
		local k = e.k
		if k == "VNIL" or k == "VFALSE"then
			pc = self.NO_JUMP  -- always false; do nothing
		elseif k == "VTRUE" then
			pc = self:jump(fs)  -- always jump
		elseif k == "VJMP" then
			pc = e.info
		else
			pc = self:jumponcond(fs, e, true)
		end
		e.t = self:concat(fs, e.t, pc)  -- insert last jump in `t' list
		self:patchtohere(fs, e.f)
		e.f = self.NO_JUMP
	end

	------------------------------------------------------------------------
	--
	-- * used only in luaK:prefix()
	------------------------------------------------------------------------
	function luaK:codenot(fs, e)
		self:dischargevars(fs, e)
		local k = e.k
		if k == "VNIL" or k == "VFALSE" then
			e.k = "VTRUE"
		elseif k == "VK" or k == "VKNUM" or k == "VTRUE" then
			e.k = "VFALSE"
		elseif k == "VJMP" then
			self:invertjump(fs, e)
		elseif k == "VRELOCABLE" or k == "VNONRELOC" then
			self:discharge2anyreg(fs, e)
			self:freeexp(fs, e)
			e.info = self:codeABC(fs, "OP_NOT", 0, e.info, 0)
			e.k = "VRELOCABLE"
		else
			lua_assert(0)  -- cannot happen
		end
		-- interchange true and false lists
		e.f, e.t = e.t, e.f
		self:removevalues(fs, e.f)
		self:removevalues(fs, e.t)
	end

	------------------------------------------------------------------------
	--
	-- * used in (lparser) luaY:field(), luaY:primaryexp()
	------------------------------------------------------------------------
	function luaK:indexed(fs, t, k)
		t.aux = self:exp2RK(fs, k)
		t.k = "VINDEXED"
	end

	------------------------------------------------------------------------
	--
	-- * used only in luaK:codearith()
	------------------------------------------------------------------------
	function luaK:constfolding(op, e1, e2)
		local r
		if not self:isnumeral(e1) or not self:isnumeral(e2) then return false end
		local v1 = e1.nval
		local v2 = e2.nval
		if op == "OP_ADD" then
			r = self:numadd(v1, v2)
		elseif op == "OP_SUB" then
			r = self:numsub(v1, v2)
		elseif op == "OP_MUL" then
			r = self:nummul(v1, v2)
		elseif op == "OP_DIV" then
			if v2 == 0 then return false end  -- do not attempt to divide by 0
			r = self:numdiv(v1, v2)
		elseif op == "OP_MOD" then
			if v2 == 0 then return false end  -- do not attempt to divide by 0
			r = self:nummod(v1, v2)
		elseif op == "OP_POW" then
			r = self:numpow(v1, v2)
		elseif op == "OP_UNM" then
			r = self:numunm(v1)
		elseif op == "OP_LEN" then
			return false  -- no constant folding for 'len'
		else
			lua_assert(0)
			r = 0
		end
		if self:numisnan(r) then return false end  -- do not attempt to produce NaN
		e1.nval = r
		return true
	end

	------------------------------------------------------------------------
	--
	-- * used in luaK:prefix(), luaK:posfix()
	------------------------------------------------------------------------
	function luaK:codearith(fs, op, e1, e2)
		if self:constfolding(op, e1, e2) then
			return
		else
			local o2 = (op ~= "OP_UNM" and op ~= "OP_LEN") and self:exp2RK(fs, e2) or 0
			local o1 = self:exp2RK(fs, e1)
			if o1 > o2 then
				self:freeexp(fs, e1)
				self:freeexp(fs, e2)
			else
				self:freeexp(fs, e2)
				self:freeexp(fs, e1)
			end
			e1.info = self:codeABC(fs, op, 0, o1, o2)
			e1.k = "VRELOCABLE"
		end
	end

	------------------------------------------------------------------------
	--
	-- * used only in luaK:posfix()
	------------------------------------------------------------------------
	function luaK:codecomp(fs, op, cond, e1, e2)
		local o1 = self:exp2RK(fs, e1)
		local o2 = self:exp2RK(fs, e2)
		self:freeexp(fs, e2)
		self:freeexp(fs, e1)
		if cond == 0 and op ~= "OP_EQ" then
			-- exchange args to replace by `<' or `<='
			o1, o2 = o2, o1  -- o1 <==> o2
			cond = 1
		end
		e1.info = self:condjump(fs, op, cond, o1, o2)
		e1.k = "VJMP"
	end

	------------------------------------------------------------------------
	--
	-- * used only in (lparser) luaY:subexpr()
	------------------------------------------------------------------------
	function luaK:prefix(fs, op, e)
		local e2 = {}  -- expdesc
		e2.t, e2.f = self.NO_JUMP, self.NO_JUMP
		e2.k = "VKNUM"
		e2.nval = 0
		if op == "OPR_MINUS" then
			if not self:isnumeral(e) then
				self:exp2anyreg(fs, e)  -- cannot operate on non-numeric constants
			end
			self:codearith(fs, "OP_UNM", e, e2)
		elseif op == "OPR_NOT" then
			self:codenot(fs, e)
		elseif op == "OPR_LEN" then
			self:exp2anyreg(fs, e)  -- cannot operate on constants
			self:codearith(fs, "OP_LEN", e, e2)
		else
			lua_assert(0)
		end
	end

	------------------------------------------------------------------------
	--
	-- * used only in (lparser) luaY:subexpr()
	------------------------------------------------------------------------
	function luaK:infix(fs, op, v)
		if op == "OPR_AND" then
			self:goiftrue(fs, v)
		elseif op == "OPR_OR" then
			self:goiffalse(fs, v)
		elseif op == "OPR_CONCAT" then
			self:exp2nextreg(fs, v)  -- operand must be on the 'stack'
		elseif op == "OPR_ADD" or op == "OPR_SUB" or
					 op == "OPR_MUL" or op == "OPR_DIV" or
					 op == "OPR_MOD" or op == "OPR_POW" then
			if not self:isnumeral(v) then self:exp2RK(fs, v) end
		else
			self:exp2RK(fs, v)
		end
	end

	------------------------------------------------------------------------
	--
	-- * used only in (lparser) luaY:subexpr()
	------------------------------------------------------------------------
	-- table lookups to simplify testing
	luaK.arith_op = {
		OPR_ADD = "OP_ADD", OPR_SUB = "OP_SUB", OPR_MUL = "OP_MUL",
		OPR_DIV = "OP_DIV", OPR_MOD = "OP_MOD", OPR_POW = "OP_POW",
	}
	luaK.comp_op = {
		OPR_EQ = "OP_EQ", OPR_NE = "OP_EQ", OPR_LT = "OP_LT",
		OPR_LE = "OP_LE", OPR_GT = "OP_LT", OPR_GE = "OP_LE",
	}
	luaK.comp_cond = {
		OPR_EQ = 1, OPR_NE = 0, OPR_LT = 1,
		OPR_LE = 1, OPR_GT = 0, OPR_GE = 0,
	}
	function luaK:posfix(fs, op, e1, e2)
		-- needed because e1 = e2 doesn't copy values...
		-- * in 5.0.x, only k/info/aux/t/f copied, t for AND, f for OR
		--   but here, all elements are copied for completeness' sake
		local function copyexp(e1, e2)
			e1.k = e2.k
			e1.info = e2.info; e1.aux = e2.aux
			e1.nval = e2.nval
			e1.t = e2.t; e1.f = e2.f
		end
		if op == "OPR_AND" then
			lua_assert(e1.t == self.NO_JUMP)  -- list must be closed
			self:dischargevars(fs, e2)
			e2.f = self:concat(fs, e2.f, e1.f)
			copyexp(e1, e2)
		elseif op == "OPR_OR" then
			lua_assert(e1.f == self.NO_JUMP)  -- list must be closed
			self:dischargevars(fs, e2)
			e2.t = self:concat(fs, e2.t, e1.t)
			copyexp(e1, e2)
		elseif op == "OPR_CONCAT" then
			self:exp2val(fs, e2)
			if e2.k == "VRELOCABLE" and luaP:GET_OPCODE(self:getcode(fs, e2)) == "OP_CONCAT" then
				lua_assert(e1.info == luaP:GETARG_B(self:getcode(fs, e2)) - 1)
				self:freeexp(fs, e1)
				luaP:SETARG_B(self:getcode(fs, e2), e1.info)
				e1.k = "VRELOCABLE"
				e1.info = e2.info
			else
				self:exp2nextreg(fs, e2)  -- operand must be on the 'stack'
				self:codearith(fs, "OP_CONCAT", e1, e2)
			end
		else
			-- the following uses a table lookup in place of conditionals
			local arith = self.arith_op[op]
			if arith then
				self:codearith(fs, arith, e1, e2)
			else
				local comp = self.comp_op[op]
				if comp then
					self:codecomp(fs, comp, self.comp_cond[op], e1, e2)
				else
					lua_assert(0)
				end
			end--if arith
		end--if op
	end

	------------------------------------------------------------------------
	-- adjusts debug information for last instruction written, in order to
	-- change the line where item comes into existence
	-- * used in (lparser) luaY:funcargs(), luaY:forbody(), luaY:funcstat()
	------------------------------------------------------------------------
	function luaK:fixline(fs, line)
		fs.f.lineinfo[fs.pc - 1] = line
	end

	------------------------------------------------------------------------
	-- general function to write an instruction into the instruction buffer,
	-- sets debug information too
	-- * used in luaK:codeABC(), luaK:codeABx()
	-- * called directly by (lparser) luaY:whilestat()
	------------------------------------------------------------------------
	function luaK:code(fs, i, line)
		local f = fs.f
		self:dischargejpc(fs)  -- 'pc' will change
		-- put new instruction in code array
		luaY:growvector(fs.L, f.code, fs.pc, f.sizecode, nil,
										luaY.MAX_INT, "code size overflow")
		f.code[fs.pc] = i
		-- save corresponding line information
		luaY:growvector(fs.L, f.lineinfo, fs.pc, f.sizelineinfo, nil,
										luaY.MAX_INT, "code size overflow")
		f.lineinfo[fs.pc] = line
		local pc = fs.pc
		fs.pc = fs.pc + 1
		return pc
	end

	------------------------------------------------------------------------
	-- writes an instruction of type ABC
	-- * calls luaK:code()
	------------------------------------------------------------------------
	function luaK:codeABC(fs, o, a, b, c)
		lua_assert(luaP:getOpMode(o) == luaP.OpMode.iABC)
		lua_assert(luaP:getBMode(o) ~= luaP.OpArgMask.OpArgN or b == 0)
		lua_assert(luaP:getCMode(o) ~= luaP.OpArgMask.OpArgN or c == 0)
		return self:code(fs, luaP:CREATE_ABC(o, a, b, c), fs.ls.lastline)
	end

	------------------------------------------------------------------------
	-- writes an instruction of type ABx
	-- * calls luaK:code(), called by luaK:codeAsBx()
	------------------------------------------------------------------------
	function luaK:codeABx(fs, o, a, bc)
		lua_assert(luaP:getOpMode(o) == luaP.OpMode.iABx or
							 luaP:getOpMode(o) == luaP.OpMode.iAsBx)
		lua_assert(luaP:getCMode(o) == luaP.OpArgMask.OpArgN)
		return self:code(fs, luaP:CREATE_ABx(o, a, bc), fs.ls.lastline)
	end

	------------------------------------------------------------------------
	--
	-- * used in (lparser) luaY:closelistfield(), luaY:lastlistfield()
	------------------------------------------------------------------------
	function luaK:setlist(fs, base, nelems, tostore)
		local c = math.floor((nelems - 1)/luaP.LFIELDS_PER_FLUSH) + 1
		local b = (tostore == luaY.LUA_MULTRET) and 0 or tostore
		lua_assert(tostore ~= 0)
		if c <= luaP.MAXARG_C then
			self:codeABC(fs, "OP_SETLIST", base, b, c)
		else
			self:codeABC(fs, "OP_SETLIST", base, b, 0)
			self:code(fs, luaP:CREATE_Inst(c), fs.ls.lastline)
		end
		fs.freereg = base + 1  -- free registers with list values
	end




	--dofile("lparser.lua")

	--[[--------------------------------------------------------------------
	-- Expression descriptor
	-- * expkind changed to string constants; luaY:assignment was the only
	--   function to use a relational operator with this enumeration
	-- VVOID       -- no value
	-- VNIL        -- no value
	-- VTRUE       -- no value
	-- VFALSE      -- no value
	-- VK          -- info = index of constant in 'k'
	-- VKNUM       -- nval = numerical value
	-- VLOCAL      -- info = local register
	-- VUPVAL,     -- info = index of upvalue in 'upvalues'
	-- VGLOBAL     -- info = index of table; aux = index of global name in 'k'
	-- VINDEXED    -- info = table register; aux = index register (or 'k')
	-- VJMP        -- info = instruction pc
	-- VRELOCABLE  -- info = instruction pc
	-- VNONRELOC   -- info = result register
	-- VCALL       -- info = instruction pc
	-- VVARARG     -- info = instruction pc
	} ----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	-- * expdesc in Lua 5.1.x has a union u and another struct s; this Lua
	--   implementation ignores all instances of u and s usage
	-- struct expdesc:
	--   k  -- (enum: expkind)
	--   info, aux -- (int, int)
	--   nval -- (lua_Number)
	--   t  -- patch list of 'exit when true'
	--   f  -- patch list of 'exit when false'
	----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	-- struct upvaldesc:
	--   k  -- (lu_byte)
	--   info -- (lu_byte)
	----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	-- state needed to generate code for a given function
	-- struct FuncState:
	--   f  -- current function header (table: Proto)
	--   h  -- table to find (and reuse) elements in 'k' (table: Table)
	--   prev  -- enclosing function (table: FuncState)
	--   ls  -- lexical state (table: LexState)
	--   L  -- copy of the Lua state (table: lua_State)
	--   bl  -- chain of current blocks (table: BlockCnt)
	--   pc  -- next position to code (equivalent to 'ncode')
	--   lasttarget   -- 'pc' of last 'jump target'
	--   jpc  -- list of pending jumps to 'pc'
	--   freereg  -- first free register
	--   nk  -- number of elements in 'k'
	--   np  -- number of elements in 'p'
	--   nlocvars  -- number of elements in 'locvars'
	--   nactvar  -- number of active local variables
	--   upvalues[LUAI_MAXUPVALUES]  -- upvalues (table: upvaldesc)
	--   actvar[LUAI_MAXVARS]  -- declared-variable stack
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- constants used by parser
	-- * picks up duplicate values from luaX if required
	------------------------------------------------------------------------
	luaY.LUA_QS = luaX.LUA_QS or "'%s'"  -- (from luaconf.h)

	luaY.SHRT_MAX = 32767 -- (from <limits.h>)
	luaY.LUAI_MAXVARS = 200  -- (luaconf.h)
	luaY.LUAI_MAXUPVALUES = 60  -- (luaconf.h)
	luaY.MAX_INT = luaX.MAX_INT or 2147483645  -- (from llimits.h)
		-- * INT_MAX-2 for 32-bit systems
	luaY.LUAI_MAXCCALLS = 200  -- (from luaconf.h)

	luaY.VARARG_HASARG = 1  -- (from lobject.h)
	-- NOTE: HASARG_MASK is value-specific
	luaY.HASARG_MASK = 2 -- this was added for a bitop in parlist()
	luaY.VARARG_ISVARARG = 2
	-- NOTE: there is some value-specific code that involves VARARG_NEEDSARG
	luaY.VARARG_NEEDSARG = 4

	luaY.LUA_MULTRET = -1  -- (lua.h)

	--[[--------------------------------------------------------------------
	-- other functions
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- LUA_QL describes how error messages quote program elements.
	-- CHANGE it if you want a different appearance. (from luaconf.h)
	------------------------------------------------------------------------
	function luaY:LUA_QL(x)
		return "'"..x.."'"
	end

	------------------------------------------------------------------------
	-- this is a stripped-down luaM_growvector (from lmem.h) which is a
	-- macro based on luaM_growaux (in lmem.c); all the following does is
	-- reproduce the size limit checking logic of the original function
	-- so that error behaviour is identical; all arguments preserved for
	-- convenience, even those which are unused
	-- * set the t field to nil, since this originally does a sizeof(t)
	-- * size (originally a pointer) is never updated, their final values
	--   are set by luaY:close_func(), so overall things should still work
	------------------------------------------------------------------------
	function luaY:growvector(L, v, nelems, size, t, limit, e)
		if nelems >= limit then
			error(e)  -- was luaG_runerror
		end
	end

	------------------------------------------------------------------------
	-- initialize a new function prototype structure (from lfunc.c)
	-- * used only in open_func()
	------------------------------------------------------------------------
	function luaY:newproto(L)
		local f = {} -- Proto
		-- luaC_link(L, obj2gco(f), LUA_TPROTO); /* GC */
		f.k = {}
		f.sizek = 0
		f.p = {}
		f.sizep = 0
		f.code = {}
		f.sizecode = 0
		f.sizelineinfo = 0
		f.sizeupvalues = 0
		f.nups = 0
		f.upvalues = {}
		f.numparams = 0
		f.is_vararg = 0
		f.maxstacksize = 0
		f.lineinfo = {}
		f.sizelocvars = 0
		f.locvars = {}
		f.lineDefined = 0
		f.lastlinedefined = 0
		f.source = nil
		return f
	end

	------------------------------------------------------------------------
	-- converts an integer to a "floating point byte", represented as
	-- (eeeeexxx), where the real value is (1xxx) * 2^(eeeee - 1) if
	-- eeeee != 0 and (xxx) otherwise.
	------------------------------------------------------------------------
	function luaY:int2fb(x)
		local e = 0  -- exponent
		while x >= 16 do
			x = math.floor((x + 1) / 2)
			e = e + 1
		end
		if x < 8 then
			return x
		else
			return ((e + 1) * 8) + (x - 8)
		end
	end

	--[[--------------------------------------------------------------------
	-- parser functions
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- true of the kind of expression produces multiple return values
	------------------------------------------------------------------------
	function luaY:hasmultret(k)
		return k == "VCALL" or k == "VVARARG"
	end

	------------------------------------------------------------------------
	-- convenience function to access active local i, returns entry
	------------------------------------------------------------------------
	function luaY:getlocvar(fs, i)
		return fs.f.locvars[ fs.actvar[i] ]
	end

	------------------------------------------------------------------------
	-- check a limit, string m provided as an error message
	------------------------------------------------------------------------
	function luaY:checklimit(fs, v, l, m)
		if v > l then self:errorlimit(fs, l, m) end
	end

	--[[--------------------------------------------------------------------
	-- nodes for block list (list of active blocks)
	-- struct BlockCnt:
	--   previous  -- chain (table: BlockCnt)
	--   breaklist  -- list of jumps out of this loop
	--   nactvar  -- # active local variables outside the breakable structure
	--   upval  -- true if some variable in the block is an upvalue (boolean)
	--   isbreakable  -- true if 'block' is a loop (boolean)
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- prototypes for recursive non-terminal functions
	------------------------------------------------------------------------
	-- prototypes deleted; not required in Lua

	------------------------------------------------------------------------
	-- reanchor if last token is has a constant string, see close_func()
	-- * used only in close_func()
	------------------------------------------------------------------------
	function luaY:anchor_token(ls)
		if ls.t.token == "TK_NAME" or ls.t.token == "TK_STRING" then
			-- not relevant to Lua implementation of parser
			-- local ts = ls.t.seminfo
			-- luaX_newstring(ls, getstr(ts), ts->tsv.len); /* C */
		end
	end

	------------------------------------------------------------------------
	-- throws a syntax error if token expected is not there
	------------------------------------------------------------------------
	function luaY:error_expected(ls, token)
		luaX:syntaxerror(ls,
			string.format(self.LUA_QS.." expected", luaX:token2str(ls, token)))
	end

	------------------------------------------------------------------------
	-- prepares error message for display, for limits exceeded
	-- * used only in checklimit()
	------------------------------------------------------------------------
	function luaY:errorlimit(fs, limit, what)
		local msg = (fs.f.linedefined == 0) and
			string.format("main function has more than %d %s", limit, what) or
			string.format("function at line %d has more than %d %s",
										fs.f.linedefined, limit, what)
		luaX:lexerror(fs.ls, msg, 0)
	end

	------------------------------------------------------------------------
	-- tests for a token, returns outcome
	-- * return value changed to boolean
	------------------------------------------------------------------------
	function luaY:testnext(ls, c)
		if ls.t.token == c then
			luaX:next(ls)
			return true
		else
			return false
		end
	end

	------------------------------------------------------------------------
	-- check for existence of a token, throws error if not found
	------------------------------------------------------------------------
	function luaY:check(ls, c)
		if ls.t.token ~= c then
			self:error_expected(ls, c)
		end
	end

	------------------------------------------------------------------------
	-- verify existence of a token, then skip it
	------------------------------------------------------------------------
	function luaY:checknext(ls, c)
		self:check(ls, c)
		luaX:next(ls)
	end

	------------------------------------------------------------------------
	-- throws error if condition not matched
	------------------------------------------------------------------------
	function luaY:check_condition(ls, c, msg)
		if not c then luaX:syntaxerror(ls, msg) end
	end

	------------------------------------------------------------------------
	-- verifies token conditions are met or else throw error
	------------------------------------------------------------------------
	function luaY:check_match(ls, what, who, where)
		if not self:testnext(ls, what) then
			if where == ls.linenumber then
				self:error_expected(ls, what)
			else
				luaX:syntaxerror(ls, string.format(
					self.LUA_QS.." expected (to close "..self.LUA_QS.." at line %d)",
					luaX:token2str(ls, what), luaX:token2str(ls, who), where))
			end
		end
	end

	------------------------------------------------------------------------
	-- expect that token is a name, return the name
	------------------------------------------------------------------------
	function luaY:str_checkname(ls)
		self:check(ls, "TK_NAME")
		local ts = ls.t.seminfo
		luaX:next(ls)
		return ts
	end

	------------------------------------------------------------------------
	-- initialize a struct expdesc, expression description data structure
	------------------------------------------------------------------------
	function luaY:init_exp(e, k, i)
		e.f, e.t = luaK.NO_JUMP, luaK.NO_JUMP
		e.k = k
		e.info = i
	end

	------------------------------------------------------------------------
	-- adds given string s in string pool, sets e as VK
	------------------------------------------------------------------------
	function luaY:codestring(ls, e, s)
		self:init_exp(e, "VK", luaK:stringK(ls.fs, s))
	end

	------------------------------------------------------------------------
	-- consume a name token, adds it to string pool, sets e as VK
	------------------------------------------------------------------------
	function luaY:checkname(ls, e)
		self:codestring(ls, e, self:str_checkname(ls))
	end

	------------------------------------------------------------------------
	-- creates struct entry for a local variable
	-- * used only in new_localvar()
	------------------------------------------------------------------------
	function luaY:registerlocalvar(ls, varname)
		local fs = ls.fs
		local f = fs.f
		self:growvector(ls.L, f.locvars, fs.nlocvars, f.sizelocvars,
										nil, self.SHRT_MAX, "too many local variables")
		-- loop to initialize empty f.locvar positions not required
		f.locvars[fs.nlocvars] = {} -- LocVar
		f.locvars[fs.nlocvars].varname = varname
		-- luaC_objbarrier(ls.L, f, varname) /* GC */
		local nlocvars = fs.nlocvars
		fs.nlocvars = fs.nlocvars + 1
		return nlocvars
	end

	------------------------------------------------------------------------
	-- creates a new local variable given a name and an offset from nactvar
	-- * used in fornum(), forlist(), parlist(), body()
	------------------------------------------------------------------------
	function luaY:new_localvarliteral(ls, v, n)
		self:new_localvar(ls, v, n)
	end

	------------------------------------------------------------------------
	-- register a local variable, set in active variable list
	------------------------------------------------------------------------
	function luaY:new_localvar(ls, name, n)
		local fs = ls.fs
		self:checklimit(fs, fs.nactvar + n + 1, self.LUAI_MAXVARS, "local variables")
		fs.actvar[fs.nactvar + n] = self:registerlocalvar(ls, name)
	end

	------------------------------------------------------------------------
	-- adds nvars number of new local variables, set debug information
	------------------------------------------------------------------------
	function luaY:adjustlocalvars(ls, nvars)
		local fs = ls.fs
		fs.nactvar = fs.nactvar + nvars
		for i = nvars, 1, -1 do
			self:getlocvar(fs, fs.nactvar - i).startpc = fs.pc
		end
	end

	------------------------------------------------------------------------
	-- removes a number of locals, set debug information
	------------------------------------------------------------------------
	function luaY:removevars(ls, tolevel)
		local fs = ls.fs
		while fs.nactvar > tolevel do
			fs.nactvar = fs.nactvar - 1
			self:getlocvar(fs, fs.nactvar).endpc = fs.pc
		end
	end

	------------------------------------------------------------------------
	-- returns an existing upvalue index based on the given name, or
	-- creates a new upvalue struct entry and returns the new index
	-- * used only in singlevaraux()
	------------------------------------------------------------------------
	function luaY:indexupvalue(fs, name, v)
		local f = fs.f
		for i = 0, f.nups - 1 do
			if fs.upvalues[i].k == v.k and fs.upvalues[i].info == v.info then
				lua_assert(f.upvalues[i] == name)
				return i
			end
		end
		-- new one
		self:checklimit(fs, f.nups + 1, self.LUAI_MAXUPVALUES, "upvalues")
		self:growvector(fs.L, f.upvalues, f.nups, f.sizeupvalues,
										nil, self.MAX_INT, "")
		-- loop to initialize empty f.upvalues positions not required
		f.upvalues[f.nups] = name
		-- luaC_objbarrier(fs->L, f, name); /* GC */
		lua_assert(v.k == "VLOCAL" or v.k == "VUPVAL")
		-- this is a partial copy; only k & info fields used
		fs.upvalues[f.nups] = { k = v.k, info = v.info }
		local nups = f.nups
		f.nups = f.nups + 1
		return nups
	end

	------------------------------------------------------------------------
	-- search the local variable namespace of the given fs for a match
	-- * used only in singlevaraux()
	------------------------------------------------------------------------
	function luaY:searchvar(fs, n)
		for i = fs.nactvar - 1, 0, -1 do
			if n == self:getlocvar(fs, i).varname then
				return i
			end
		end
		return -1  -- not found
	end

	------------------------------------------------------------------------
	-- * mark upvalue flags in function states up to a given level
	-- * used only in singlevaraux()
	------------------------------------------------------------------------
	function luaY:markupval(fs, level)
		local bl = fs.bl
		while bl and bl.nactvar > level do bl = bl.previous end
		if bl then bl.upval = true end
	end

	------------------------------------------------------------------------
	-- handle locals, globals and upvalues and related processing
	-- * search mechanism is recursive, calls itself to search parents
	-- * used only in singlevar()
	------------------------------------------------------------------------
	function luaY:singlevaraux(fs, n, var, base)
		if fs == nil then  -- no more levels?
			self:init_exp(var, "VGLOBAL", luaP.NO_REG)  -- default is global variable
			return "VGLOBAL"
		else
			local v = self:searchvar(fs, n)  -- look up at current level
			if v >= 0 then
				self:init_exp(var, "VLOCAL", v)
				if base == 0 then
					self:markupval(fs, v)  -- local will be used as an upval
				end
				return "VLOCAL"
			else  -- not found at current level; try upper one
				if self:singlevaraux(fs.prev, n, var, 0) == "VGLOBAL" then
					return "VGLOBAL"
				end
				var.info = self:indexupvalue(fs, n, var)  -- else was LOCAL or UPVAL
				var.k = "VUPVAL"  -- upvalue in this level
				return "VUPVAL"
			end--if v
		end--if fs
	end

	------------------------------------------------------------------------
	-- consume a name token, creates a variable (global|local|upvalue)
	-- * used in prefixexp(), funcname()
	------------------------------------------------------------------------
	function luaY:singlevar(ls, var)
		local varname = self:str_checkname(ls)
		local fs = ls.fs
		if self:singlevaraux(fs, varname, var, 1) == "VGLOBAL" then
			var.info = luaK:stringK(fs, varname)  -- info points to global name
		end
	end

	------------------------------------------------------------------------
	-- adjust RHS to match LHS in an assignment
	-- * used in assignment(), forlist(), localstat()
	------------------------------------------------------------------------
	function luaY:adjust_assign(ls, nvars, nexps, e)
		local fs = ls.fs
		local extra = nvars - nexps
		if self:hasmultret(e.k) then
			extra = extra + 1  -- includes call itself
			if extra <= 0 then extra = 0 end
			luaK:setreturns(fs, e, extra)  -- last exp. provides the difference
			if extra > 1 then luaK:reserveregs(fs, extra - 1) end
		else
			if e.k ~= "VVOID" then luaK:exp2nextreg(fs, e) end  -- close last expression
			if extra > 0 then
				local reg = fs.freereg
				luaK:reserveregs(fs, extra)
				luaK:_nil(fs, reg, extra)
			end
		end
	end

	------------------------------------------------------------------------
	-- tracks and limits parsing depth, assert check at end of parsing
	------------------------------------------------------------------------
	function luaY:enterlevel(ls)
		ls.L.nCcalls = ls.L.nCcalls + 1
		if ls.L.nCcalls > self.LUAI_MAXCCALLS then
			luaX:lexerror(ls, "chunk has too many syntax levels", 0)
		end
	end

	------------------------------------------------------------------------
	-- tracks parsing depth, a pair with luaY:enterlevel()
	------------------------------------------------------------------------
	function luaY:leavelevel(ls)
		ls.L.nCcalls = ls.L.nCcalls - 1
	end

	------------------------------------------------------------------------
	-- enters a code unit, initializes elements
	------------------------------------------------------------------------
	function luaY:enterblock(fs, bl, isbreakable)
		bl.breaklist = luaK.NO_JUMP
		bl.isbreakable = isbreakable
		bl.nactvar = fs.nactvar
		bl.upval = false
		bl.previous = fs.bl
		fs.bl = bl
		lua_assert(fs.freereg == fs.nactvar)
	end

	------------------------------------------------------------------------
	-- leaves a code unit, close any upvalues
	------------------------------------------------------------------------
	function luaY:leaveblock(fs)
		local bl = fs.bl
		fs.bl = bl.previous
		self:removevars(fs.ls, bl.nactvar)
		if bl.upval then
			luaK:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
		end
		-- a block either controls scope or breaks (never both)
		lua_assert(not bl.isbreakable or not bl.upval)
		lua_assert(bl.nactvar == fs.nactvar)
		fs.freereg = fs.nactvar  -- free registers
		luaK:patchtohere(fs, bl.breaklist)
	end

	------------------------------------------------------------------------
	-- implement the instantiation of a function prototype, append list of
	-- upvalues after the instantiation instruction
	-- * used only in body()
	------------------------------------------------------------------------
	function luaY:pushclosure(ls, func, v)
		local fs = ls.fs
		local f = fs.f
		self:growvector(ls.L, f.p, fs.np, f.sizep, nil,
										luaP.MAXARG_Bx, "constant table overflow")
		-- loop to initialize empty f.p positions not required
		f.p[fs.np] = func.f
		fs.np = fs.np + 1
		-- luaC_objbarrier(ls->L, f, func->f); /* C */
		self:init_exp(v, "VRELOCABLE", luaK:codeABx(fs, "OP_CLOSURE", 0, fs.np - 1))
		for i = 0, func.f.nups - 1 do
			local o = (func.upvalues[i].k == "VLOCAL") and "OP_MOVE" or "OP_GETUPVAL"
			luaK:codeABC(fs, o, 0, func.upvalues[i].info, 0)
		end
	end

	------------------------------------------------------------------------
	-- opening of a function
	------------------------------------------------------------------------
	function luaY:open_func(ls, fs)
		local L = ls.L
		local f = self:newproto(ls.L)
		fs.f = f
		fs.prev = ls.fs  -- linked list of funcstates
		fs.ls = ls
		fs.L = L
		ls.fs = fs
		fs.pc = 0
		fs.lasttarget = -1
		fs.jpc = luaK.NO_JUMP
		fs.freereg = 0
		fs.nk = 0
		fs.np = 0
		fs.nlocvars = 0
		fs.nactvar = 0
		fs.bl = nil
		f.source = ls.source
		f.maxstacksize = 2  -- registers 0/1 are always valid
		fs.h = {}  -- constant table; was luaH_new call
		-- anchor table of constants and prototype (to avoid being collected)
		-- sethvalue2s(L, L->top, fs->h); incr_top(L); /* C */
		-- setptvalue2s(L, L->top, f); incr_top(L);
	end

	------------------------------------------------------------------------
	-- closing of a function
	------------------------------------------------------------------------
	function luaY:close_func(ls)
		local L = ls.L
		local fs = ls.fs
		local f = fs.f
		self:removevars(ls, 0)
		luaK:ret(fs, 0, 0)  -- final return
		-- luaM_reallocvector deleted for f->code, f->lineinfo, f->k, f->p,
		-- f->locvars, f->upvalues; not required for Lua table arrays
		f.sizecode = fs.pc
		f.sizelineinfo = fs.pc
		f.sizek = fs.nk
		f.sizep = fs.np
		f.sizelocvars = fs.nlocvars
		f.sizeupvalues = f.nups
		--lua_assert(luaG_checkcode(f))  -- currently not implemented
		lua_assert(fs.bl == nil)
		ls.fs = fs.prev
		-- the following is not required for this implementation; kept here
		-- for completeness
		-- L->top -= 2;  /* remove table and prototype from the stack */
		-- last token read was anchored in defunct function; must reanchor it
		if fs then self:anchor_token(ls) end
	end

	------------------------------------------------------------------------
	-- parser initialization function
	-- * note additional sub-tables needed for LexState, FuncState
	------------------------------------------------------------------------
	function luaY:parser(L, z, buff, name)
		local lexstate = {}  -- LexState
					lexstate.t = {}
					lexstate.lookahead = {}
		local funcstate = {}  -- FuncState
					funcstate.upvalues = {}
					funcstate.actvar = {}
		-- the following nCcalls initialization added for convenience
		L.nCcalls = 0
		lexstate.buff = buff
		luaX:setinput(L, lexstate, z, name)
		self:open_func(lexstate, funcstate)
		funcstate.f.is_vararg = self.VARARG_ISVARARG  -- main func. is always vararg
		luaX:next(lexstate)  -- read first token
		self:chunk(lexstate)
		self:check(lexstate, "TK_EOS")
		self:close_func(lexstate)
		lua_assert(funcstate.prev == nil)
		lua_assert(funcstate.f.nups == 0)
		lua_assert(lexstate.fs == nil)
		return funcstate.f
	end

	--[[--------------------------------------------------------------------
	-- GRAMMAR RULES
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- parse a function name suffix, for function call specifications
	-- * used in primaryexp(), funcname()
	------------------------------------------------------------------------
	function luaY:field(ls, v)
		-- field -> ['.' | ':'] NAME
		local fs = ls.fs
		local key = {}  -- expdesc
		luaK:exp2anyreg(fs, v)
		luaX:next(ls)  -- skip the dot or colon
		self:checkname(ls, key)
		luaK:indexed(fs, v, key)
	end

	------------------------------------------------------------------------
	-- parse a table indexing suffix, for constructors, expressions
	-- * used in recfield(), primaryexp()
	------------------------------------------------------------------------
	function luaY:yindex(ls, v)
		-- index -> '[' expr ']'
		luaX:next(ls)  -- skip the '['
		self:expr(ls, v)
		luaK:exp2val(ls.fs, v)
		self:checknext(ls, "]")
	end

	--[[--------------------------------------------------------------------
	-- Rules for Constructors
	----------------------------------------------------------------------]]

	--[[--------------------------------------------------------------------
	-- struct ConsControl:
	--   v  -- last list item read (table: struct expdesc)
	--   t  -- table descriptor (table: struct expdesc)
	--   nh  -- total number of 'record' elements
	--   na  -- total number of array elements
	--   tostore  -- number of array elements pending to be stored
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- parse a table record (hash) field
	-- * used in constructor()
	------------------------------------------------------------------------
	function luaY:recfield(ls, cc)
		-- recfield -> (NAME | '['exp1']') = exp1
		local fs = ls.fs
		local reg = ls.fs.freereg
		local key, val = {}, {}  -- expdesc
		if ls.t.token == "TK_NAME" then
			self:checklimit(fs, cc.nh, self.MAX_INT, "items in a constructor")
			self:checkname(ls, key)
		else  -- ls->t.token == '['
			self:yindex(ls, key)
		end
		cc.nh = cc.nh + 1
		self:checknext(ls, "=")
		local rkkey = luaK:exp2RK(fs, key)
		self:expr(ls, val)
		luaK:codeABC(fs, "OP_SETTABLE", cc.t.info, rkkey, luaK:exp2RK(fs, val))
		fs.freereg = reg  -- free registers
	end

	------------------------------------------------------------------------
	-- emit a set list instruction if enough elements (LFIELDS_PER_FLUSH)
	-- * used in constructor()
	------------------------------------------------------------------------
	function luaY:closelistfield(fs, cc)
		if cc.v.k == "VVOID" then return end  -- there is no list item
		luaK:exp2nextreg(fs, cc.v)
		cc.v.k = "VVOID"
		if cc.tostore == luaP.LFIELDS_PER_FLUSH then
			luaK:setlist(fs, cc.t.info, cc.na, cc.tostore)  -- flush
			cc.tostore = 0  -- no more items pending
		end
	end

	------------------------------------------------------------------------
	-- emit a set list instruction at the end of parsing list constructor
	-- * used in constructor()
	------------------------------------------------------------------------
	function luaY:lastlistfield(fs, cc)
		if cc.tostore == 0 then return end
		if self:hasmultret(cc.v.k) then
			luaK:setmultret(fs, cc.v)
			luaK:setlist(fs, cc.t.info, cc.na, self.LUA_MULTRET)
			cc.na = cc.na - 1  -- do not count last expression (unknown number of elements)
		else
			if cc.v.k ~= "VVOID" then
				luaK:exp2nextreg(fs, cc.v)
			end
			luaK:setlist(fs, cc.t.info, cc.na, cc.tostore)
		end
	end

	------------------------------------------------------------------------
	-- parse a table list (array) field
	-- * used in constructor()
	------------------------------------------------------------------------
	function luaY:listfield(ls, cc)
		self:expr(ls, cc.v)
		self:checklimit(ls.fs, cc.na, self.MAX_INT, "items in a constructor")
		cc.na = cc.na + 1
		cc.tostore = cc.tostore + 1
	end

	------------------------------------------------------------------------
	-- parse a table constructor
	-- * used in funcargs(), simpleexp()
	------------------------------------------------------------------------
	function luaY:constructor(ls, t)
		-- constructor -> '{' [ field { fieldsep field } [ fieldsep ] ] '}'
		-- field -> recfield | listfield
		-- fieldsep -> ',' | ';'
		local fs = ls.fs
		local line = ls.linenumber
		local pc = luaK:codeABC(fs, "OP_NEWTABLE", 0, 0, 0)
		local cc = {}  -- ConsControl
					cc.v = {}
		cc.na, cc.nh, cc.tostore = 0, 0, 0
		cc.t = t
		self:init_exp(t, "VRELOCABLE", pc)
		self:init_exp(cc.v, "VVOID", 0)  -- no value (yet)
		luaK:exp2nextreg(ls.fs, t)  -- fix it at stack top (for gc)
		self:checknext(ls, "{")
		repeat
			lua_assert(cc.v.k == "VVOID" or cc.tostore > 0)
			if ls.t.token == "}" then break end
			self:closelistfield(fs, cc)
			local c = ls.t.token

			if c == "TK_NAME" then  -- may be listfields or recfields
				luaX:lookahead(ls)
				if ls.lookahead.token ~= "=" then  -- expression?
					self:listfield(ls, cc)
				else
					self:recfield(ls, cc)
				end
			elseif c == "[" then  -- constructor_item -> recfield
				self:recfield(ls, cc)
			else  -- constructor_part -> listfield
				self:listfield(ls, cc)
			end
		until not self:testnext(ls, ",") and not self:testnext(ls, ";")
		self:check_match(ls, "}", "{", line)
		self:lastlistfield(fs, cc)
		luaP:SETARG_B(fs.f.code[pc], self:int2fb(cc.na)) -- set initial array size
		luaP:SETARG_C(fs.f.code[pc], self:int2fb(cc.nh)) -- set initial table size
	end

	-- }======================================================================

	------------------------------------------------------------------------
	-- parse the arguments (parameters) of a function declaration
	-- * used in body()
	------------------------------------------------------------------------
	function luaY:parlist(ls)
		-- parlist -> [ param { ',' param } ]
		local fs = ls.fs
		local f = fs.f
		local nparams = 0
		f.is_vararg = 0
		if ls.t.token ~= ")" then  -- is 'parlist' not empty?
			repeat
				local c = ls.t.token
				if c == "TK_NAME" then  -- param -> NAME
					self:new_localvar(ls, self:str_checkname(ls), nparams)
					nparams = nparams + 1
				elseif c == "TK_DOTS" then  -- param -> `...'
					luaX:next(ls)
	-- [[
	-- #if defined(LUA_COMPAT_VARARG)
					-- use `arg' as default name
					self:new_localvarliteral(ls, "arg", nparams)
					nparams = nparams + 1
					f.is_vararg = self.VARARG_HASARG + self.VARARG_NEEDSARG
	-- #endif
	--]]
					f.is_vararg = f.is_vararg + self.VARARG_ISVARARG
				else
					luaX:syntaxerror(ls, "<name> or "..self:LUA_QL("...").." expected")
				end
			until f.is_vararg ~= 0 or not self:testnext(ls, ",")
		end--if
		self:adjustlocalvars(ls, nparams)
		-- NOTE: the following works only when HASARG_MASK is 2!
		f.numparams = fs.nactvar - (f.is_vararg % self.HASARG_MASK)
		luaK:reserveregs(fs, fs.nactvar)  -- reserve register for parameters
	end

	------------------------------------------------------------------------
	-- parse function declaration body
	-- * used in simpleexp(), localfunc(), funcstat()
	------------------------------------------------------------------------
	function luaY:body(ls, e, needself, line)
		-- body ->  '(' parlist ')' chunk END
		local new_fs = {}  -- FuncState
					new_fs.upvalues = {}
					new_fs.actvar = {}
		self:open_func(ls, new_fs)
		new_fs.f.lineDefined = line
		self:checknext(ls, "(")
		if needself then
			self:new_localvarliteral(ls, "self", 0)
			self:adjustlocalvars(ls, 1)
		end
		self:parlist(ls)
		self:checknext(ls, ")")
		self:chunk(ls)
		new_fs.f.lastlinedefined = ls.linenumber
		self:check_match(ls, "TK_END", "TK_FUNCTION", line)
		self:close_func(ls)
		self:pushclosure(ls, new_fs, e)
	end

	------------------------------------------------------------------------
	-- parse a list of comma-separated expressions
	-- * used is multiple locations
	------------------------------------------------------------------------
	function luaY:explist1(ls, v)
		-- explist1 -> expr { ',' expr }
		local n = 1  -- at least one expression
		self:expr(ls, v)
		while self:testnext(ls, ",") do
			luaK:exp2nextreg(ls.fs, v)
			self:expr(ls, v)
			n = n + 1
		end
		return n
	end

	------------------------------------------------------------------------
	-- parse the parameters of a function call
	-- * contrast with parlist(), used in function declarations
	-- * used in primaryexp()
	------------------------------------------------------------------------
	function luaY:funcargs(ls, f)
		local fs = ls.fs
		local args = {}  -- expdesc
		local nparams
		local line = ls.linenumber
		local c = ls.t.token
		if c == "(" then  -- funcargs -> '(' [ explist1 ] ')'
			if line ~= ls.lastline then
				luaX:syntaxerror(ls, "ambiguous syntax (function call x new statement)")
			end
			luaX:next(ls)
			if ls.t.token == ")" then  -- arg list is empty?
				args.k = "VVOID"
			else
				self:explist1(ls, args)
				luaK:setmultret(fs, args)
			end
			self:check_match(ls, ")", "(", line)
		elseif c == "{" then  -- funcargs -> constructor
			self:constructor(ls, args)
		elseif c == "TK_STRING" then  -- funcargs -> STRING
			self:codestring(ls, args, ls.t.seminfo)
			luaX:next(ls)  -- must use 'seminfo' before 'next'
		else
			luaX:syntaxerror(ls, "function arguments expected")
			return
		end
		lua_assert(f.k == "VNONRELOC")
		local base = f.info  -- base register for call
		if self:hasmultret(args.k) then
			nparams = self.LUA_MULTRET  -- open call
		else
			if args.k ~= "VVOID" then
				luaK:exp2nextreg(fs, args)  -- close last argument
			end
			nparams = fs.freereg - (base + 1)
		end
		self:init_exp(f, "VCALL", luaK:codeABC(fs, "OP_CALL", base, nparams + 1, 2))
		luaK:fixline(fs, line)
		fs.freereg = base + 1  -- call remove function and arguments and leaves
													 -- (unless changed) one result
	end

	--[[--------------------------------------------------------------------
	-- Expression parsing
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- parses an expression in parentheses or a single variable
	-- * used in primaryexp()
	------------------------------------------------------------------------
	function luaY:prefixexp(ls, v)
		-- prefixexp -> NAME | '(' expr ')'
		local c = ls.t.token
		if c == "(" then
			local line = ls.linenumber
			luaX:next(ls)
			self:expr(ls, v)
			self:check_match(ls, ")", "(", line)
			luaK:dischargevars(ls.fs, v)
		elseif c == "TK_NAME" then
			self:singlevar(ls, v)
		else
			luaX:syntaxerror(ls, "unexpected symbol")
		end--if c
		return
	end

	------------------------------------------------------------------------
	-- parses a prefixexp (an expression in parentheses or a single variable)
	-- or a function call specification
	-- * used in simpleexp(), assignment(), exprstat()
	------------------------------------------------------------------------
	function luaY:primaryexp(ls, v)
		-- primaryexp ->
		--    prefixexp { '.' NAME | '[' exp ']' | ':' NAME funcargs | funcargs }
		local fs = ls.fs
		self:prefixexp(ls, v)
		while true do
			local c = ls.t.token
			if c == "." then  -- field
				self:field(ls, v)
			elseif c == "[" then  -- '[' exp1 ']'
				local key = {}  -- expdesc
				luaK:exp2anyreg(fs, v)
				self:yindex(ls, key)
				luaK:indexed(fs, v, key)
			elseif c == ":" then  -- ':' NAME funcargs
				local key = {}  -- expdesc
				luaX:next(ls)
				self:checkname(ls, key)
				luaK:_self(fs, v, key)
				self:funcargs(ls, v)
			elseif c == "(" or c == "TK_STRING" or c == "{" then  -- funcargs
				luaK:exp2nextreg(fs, v)
				self:funcargs(ls, v)
			else
				return
			end--if c
		end--while
	end

	------------------------------------------------------------------------
	-- parses general expression types, constants handled here
	-- * used in subexpr()
	------------------------------------------------------------------------
	function luaY:simpleexp(ls, v)
		-- simpleexp -> NUMBER | STRING | NIL | TRUE | FALSE | ... |
		--              constructor | FUNCTION body | primaryexp
		local c = ls.t.token
		if c == "TK_NUMBER" then
			self:init_exp(v, "VKNUM", 0)
			v.nval = ls.t.seminfo
		elseif c == "TK_STRING" then
			self:codestring(ls, v, ls.t.seminfo)
		elseif c == "TK_NIL" then
			self:init_exp(v, "VNIL", 0)
		elseif c == "TK_TRUE" then
			self:init_exp(v, "VTRUE", 0)
		elseif c == "TK_FALSE" then
			self:init_exp(v, "VFALSE", 0)
		elseif c == "TK_DOTS" then  -- vararg
			local fs = ls.fs
			self:check_condition(ls, fs.f.is_vararg ~= 0,
											"cannot use "..self:LUA_QL("...").." outside a vararg function");
			-- NOTE: the following substitutes for a bitop, but is value-specific
			local is_vararg = fs.f.is_vararg
			if is_vararg >= self.VARARG_NEEDSARG then
				fs.f.is_vararg = is_vararg - self.VARARG_NEEDSARG  -- don't need 'arg'
			end
			self:init_exp(v, "VVARARG", luaK:codeABC(fs, "OP_VARARG", 0, 1, 0))
		elseif c == "{" then  -- constructor
			self:constructor(ls, v)
			return
		elseif c == "TK_FUNCTION" then
			luaX:next(ls)
			self:body(ls, v, false, ls.linenumber)
			return
		else
			self:primaryexp(ls, v)
			return
		end--if c
		luaX:next(ls)
	end

	------------------------------------------------------------------------
	-- Translates unary operators tokens if found, otherwise returns
	-- OPR_NOUNOPR. getunopr() and getbinopr() are used in subexpr().
	-- * used in subexpr()
	------------------------------------------------------------------------
	function luaY:getunopr(op)
		if op == "TK_NOT" then
			return "OPR_NOT"
		elseif op == "-" then
			return "OPR_MINUS"
		elseif op == "#" then
			return "OPR_LEN"
		else
			return "OPR_NOUNOPR"
		end
	end

	------------------------------------------------------------------------
	-- Translates binary operator tokens if found, otherwise returns
	-- OPR_NOBINOPR. Code generation uses OPR_* style tokens.
	-- * used in subexpr()
	------------------------------------------------------------------------
	luaY.getbinopr_table = {
		["+"] = "OPR_ADD",
		["-"] = "OPR_SUB",
		["*"] = "OPR_MUL",
		["/"] = "OPR_DIV",
		["%"] = "OPR_MOD",
		["^"] = "OPR_POW",
		["TK_CONCAT"] = "OPR_CONCAT",
		["TK_NE"] = "OPR_NE",
		["TK_EQ"] = "OPR_EQ",
		["<"] = "OPR_LT",
		["TK_LE"] = "OPR_LE",
		[">"] = "OPR_GT",
		["TK_GE"] = "OPR_GE",
		["TK_AND"] = "OPR_AND",
		["TK_OR"] = "OPR_OR",
	}
	function luaY:getbinopr(op)
		local opr = self.getbinopr_table[op]
		if opr then return opr else return "OPR_NOBINOPR" end
	end

	------------------------------------------------------------------------
	-- the following priority table consists of pairs of left/right values
	-- for binary operators (was a static const struct); grep for ORDER OPR
	-- * the following struct is replaced:
	--   static const struct {
	--     lu_byte left;  /* left priority for each binary operator */
	--     lu_byte right; /* right priority */
	--   } priority[] = {  /* ORDER OPR */
	------------------------------------------------------------------------
	luaY.priority = {
		{6, 6}, {6, 6}, {7, 7}, {7, 7}, {7, 7}, -- `+' `-' `/' `%'
		{10, 9}, {5, 4},                 -- power and concat (right associative)
		{3, 3}, {3, 3},                  -- equality
		{3, 3}, {3, 3}, {3, 3}, {3, 3},  -- order
		{2, 2}, {1, 1}                   -- logical (and/or)
	}

	luaY.UNARY_PRIORITY = 8  -- priority for unary operators

	------------------------------------------------------------------------
	-- Parse subexpressions. Includes handling of unary operators and binary
	-- operators. A subexpr is given the rhs priority level of the operator
	-- immediately left of it, if any (limit is -1 if none,) and if a binop
	-- is found, limit is compared with the lhs priority level of the binop
	-- in order to determine which executes first.
	------------------------------------------------------------------------

	------------------------------------------------------------------------
	-- subexpr -> (simpleexp | unop subexpr) { binop subexpr }
	-- where 'binop' is any binary operator with a priority higher than 'limit'
	-- * for priority lookups with self.priority[], 1=left and 2=right
	-- * recursively called
	-- * used in expr()
	------------------------------------------------------------------------
	function luaY:subexpr(ls, v, limit)
		self:enterlevel(ls)
		local uop = self:getunopr(ls.t.token)
		if uop ~= "OPR_NOUNOPR" then
			luaX:next(ls)
			self:subexpr(ls, v, self.UNARY_PRIORITY)
			luaK:prefix(ls.fs, uop, v)
		else
			self:simpleexp(ls, v)
		end
		-- expand while operators have priorities higher than 'limit'
		local op = self:getbinopr(ls.t.token)
		while op ~= "OPR_NOBINOPR" and self.priority[luaK.BinOpr[op] + 1][1] > limit do
			local v2 = {}  -- expdesc
			luaX:next(ls)
			luaK:infix(ls.fs, op, v)
			-- read sub-expression with higher priority
			local nextop = self:subexpr(ls, v2, self.priority[luaK.BinOpr[op] + 1][2])
			luaK:posfix(ls.fs, op, v, v2)
			op = nextop
		end
		self:leavelevel(ls)
		return op  -- return first untreated operator
	end

	------------------------------------------------------------------------
	-- Expression parsing starts here. Function subexpr is entered with the
	-- left operator (which is non-existent) priority of -1, which is lower
	-- than all actual operators. Expr information is returned in parm v.
	-- * used in multiple locations
	------------------------------------------------------------------------
	function luaY:expr(ls, v)
		self:subexpr(ls, v, 0)
	end

	-- }====================================================================

	--[[--------------------------------------------------------------------
	-- Rules for Statements
	----------------------------------------------------------------------]]

	------------------------------------------------------------------------
	-- checks next token, used as a look-ahead
	-- * returns boolean instead of 0|1
	-- * used in retstat(), chunk()
	------------------------------------------------------------------------
	function luaY:block_follow(token)
		if token == "TK_ELSE" or token == "TK_ELSEIF" or token == "TK_END"
			 or token == "TK_UNTIL" or token == "TK_EOS" then
			return true
		else
			return false
		end
	end

	------------------------------------------------------------------------
	-- parse a code block or unit
	-- * used in multiple functions
	------------------------------------------------------------------------
	function luaY:block(ls)
		-- block -> chunk
		local fs = ls.fs
		local bl = {}  -- BlockCnt
		self:enterblock(fs, bl, false)
		self:chunk(ls)
		lua_assert(bl.breaklist == luaK.NO_JUMP)
		self:leaveblock(fs)
	end

	------------------------------------------------------------------------
	-- structure to chain all variables in the left-hand side of an
	-- assignment
	-- struct LHS_assign:
	--   prev  -- (table: struct LHS_assign)
	--   v  -- variable (global, local, upvalue, or indexed) (table: expdesc)
	------------------------------------------------------------------------

	------------------------------------------------------------------------
	-- check whether, in an assignment to a local variable, the local variable
	-- is needed in a previous assignment (to a table). If so, save original
	-- local value in a safe place and use this safe copy in the previous
	-- assignment.
	-- * used in assignment()
	------------------------------------------------------------------------
	function luaY:check_conflict(ls, lh, v)
		local fs = ls.fs
		local extra = fs.freereg  -- eventual position to save local variable
		local conflict = false
		while lh do
			if lh.v.k == "VINDEXED" then
				if lh.v.info == v.info then  -- conflict?
					conflict = true
					lh.v.info = extra  -- previous assignment will use safe copy
				end
				if lh.v.aux == v.info then  -- conflict?
					conflict = true
					lh.v.aux = extra  -- previous assignment will use safe copy
				end
			end
			lh = lh.prev
		end
		if conflict then
			luaK:codeABC(fs, "OP_MOVE", fs.freereg, v.info, 0)  -- make copy
			luaK:reserveregs(fs, 1)
		end
	end

	------------------------------------------------------------------------
	-- parse a variable assignment sequence
	-- * recursively called
	-- * used in exprstat()
	------------------------------------------------------------------------
	function luaY:assignment(ls, lh, nvars)
		local e = {}  -- expdesc
		-- test was: VLOCAL <= lh->v.k && lh->v.k <= VINDEXED
		local c = lh.v.k
		self:check_condition(ls, c == "VLOCAL" or c == "VUPVAL" or c == "VGLOBAL"
												 or c == "VINDEXED", "syntax error")
		if self:testnext(ls, ",") then  -- assignment -> ',' primaryexp assignment
			local nv = {}  -- LHS_assign
						nv.v = {}
			nv.prev = lh
			self:primaryexp(ls, nv.v)
			if nv.v.k == "VLOCAL" then
				self:check_conflict(ls, lh, nv.v)
			end
			self:checklimit(ls.fs, nvars, self.LUAI_MAXCCALLS - ls.L.nCcalls,
											"variables in assignment")
			self:assignment(ls, nv, nvars + 1)
		else  -- assignment -> '=' explist1
			self:checknext(ls, "=")
			local nexps = self:explist1(ls, e)
			if nexps ~= nvars then
				self:adjust_assign(ls, nvars, nexps, e)
				if nexps > nvars then
					ls.fs.freereg = ls.fs.freereg - (nexps - nvars)  -- remove extra values
				end
			else
				luaK:setoneret(ls.fs, e)  -- close last expression
				luaK:storevar(ls.fs, lh.v, e)
				return  -- avoid default
			end
		end
		self:init_exp(e, "VNONRELOC", ls.fs.freereg - 1)  -- default assignment
		luaK:storevar(ls.fs, lh.v, e)
	end

	------------------------------------------------------------------------
	-- parse condition in a repeat statement or an if control structure
	-- * used in repeatstat(), test_then_block()
	------------------------------------------------------------------------
	function luaY:cond(ls)
		-- cond -> exp
		local v = {}  -- expdesc
		self:expr(ls, v)  -- read condition
		if v.k == "VNIL" then v.k = "VFALSE" end  -- 'falses' are all equal here
		luaK:goiftrue(ls.fs, v)
		return v.f
	end

	------------------------------------------------------------------------
	-- parse a break statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:breakstat(ls)
		-- stat -> BREAK
		local fs = ls.fs
		local bl = fs.bl
		local upval = false
		while bl and not bl.isbreakable do
			if bl.upval then upval = true end
			bl = bl.previous
		end
		if not bl then
			luaX:syntaxerror(ls, "no loop to break")
		end
		if upval then
			luaK:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
		end
		bl.breaklist = luaK:concat(fs, bl.breaklist, luaK:jump(fs))
	end

	------------------------------------------------------------------------
	-- parse a while-do control structure, body processed by block()
	-- * with dynamic array sizes, MAXEXPWHILE + EXTRAEXP limits imposed by
	--   the function's implementation can be removed
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:whilestat(ls, line)
		-- whilestat -> WHILE cond DO block END
		local fs = ls.fs
		local bl = {}  -- BlockCnt
		luaX:next(ls)  -- skip WHILE
		local whileinit = luaK:getlabel(fs)
		local condexit = self:cond(ls)
		self:enterblock(fs, bl, true)
		self:checknext(ls, "TK_DO")
		self:block(ls)
		luaK:patchlist(fs, luaK:jump(fs), whileinit)
		self:check_match(ls, "TK_END", "TK_WHILE", line)
		self:leaveblock(fs)
		luaK:patchtohere(fs, condexit)  -- false conditions finish the loop
	end

	------------------------------------------------------------------------
	-- parse a repeat-until control structure, body parsed by chunk()
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:repeatstat(ls, line)
		-- repeatstat -> REPEAT block UNTIL cond
		local fs = ls.fs
		local repeat_init = luaK:getlabel(fs)
		local bl1, bl2 = {}, {}  -- BlockCnt
		self:enterblock(fs, bl1, true)  -- loop block
		self:enterblock(fs, bl2, false)  -- scope block
		luaX:next(ls)  -- skip REPEAT
		self:chunk(ls)
		self:check_match(ls, "TK_UNTIL", "TK_REPEAT", line)
		local condexit = self:cond(ls)  -- read condition (inside scope block)
		if not bl2.upval then  -- no upvalues?
			self:leaveblock(fs)  -- finish scope
			luaK:patchlist(ls.fs, condexit, repeat_init)  -- close the loop
		else  -- complete semantics when there are upvalues
			self:breakstat(ls)  -- if condition then break
			luaK:patchtohere(ls.fs, condexit)  -- else...
			self:leaveblock(fs)  -- finish scope...
			luaK:patchlist(ls.fs, luaK:jump(fs), repeat_init)  -- and repeat
		end
		self:leaveblock(fs)  -- finish loop
	end

	------------------------------------------------------------------------
	-- parse the single expressions needed in numerical for loops
	-- * used in fornum()
	------------------------------------------------------------------------
	function luaY:exp1(ls)
		local e = {}  -- expdesc
		self:expr(ls, e)
		local k = e.k
		luaK:exp2nextreg(ls.fs, e)
		return k
	end

	------------------------------------------------------------------------
	-- parse a for loop body for both versions of the for loop
	-- * used in fornum(), forlist()
	------------------------------------------------------------------------
	function luaY:forbody(ls, base, line, nvars, isnum)
		-- forbody -> DO block
		local bl = {}  -- BlockCnt
		local fs = ls.fs
		self:adjustlocalvars(ls, 3)  -- control variables
		self:checknext(ls, "TK_DO")
		local prep = isnum and luaK:codeAsBx(fs, "OP_FORPREP", base, luaK.NO_JUMP)
											 or luaK:jump(fs)
		self:enterblock(fs, bl, false)  -- scope for declared variables
		self:adjustlocalvars(ls, nvars)
		luaK:reserveregs(fs, nvars)
		self:block(ls)
		self:leaveblock(fs)  -- end of scope for declared variables
		luaK:patchtohere(fs, prep)
		local endfor = isnum and luaK:codeAsBx(fs, "OP_FORLOOP", base, luaK.NO_JUMP)
												 or luaK:codeABC(fs, "OP_TFORLOOP", base, 0, nvars)
		luaK:fixline(fs, line)  -- pretend that `OP_FOR' starts the loop
		luaK:patchlist(fs, isnum and endfor or luaK:jump(fs), prep + 1)
	end

	------------------------------------------------------------------------
	-- parse a numerical for loop, calls forbody()
	-- * used in forstat()
	------------------------------------------------------------------------
	function luaY:fornum(ls, varname, line)
		-- fornum -> NAME = exp1,exp1[,exp1] forbody
		local fs = ls.fs
		local base = fs.freereg
		self:new_localvarliteral(ls, "(for index)", 0)
		self:new_localvarliteral(ls, "(for limit)", 1)
		self:new_localvarliteral(ls, "(for step)", 2)
		self:new_localvar(ls, varname, 3)
		self:checknext(ls, '=')
		self:exp1(ls)  -- initial value
		self:checknext(ls, ",")
		self:exp1(ls)  -- limit
		if self:testnext(ls, ",") then
			self:exp1(ls)  -- optional step
		else  -- default step = 1
			luaK:codeABx(fs, "OP_LOADK", fs.freereg, luaK:numberK(fs, 1))
			luaK:reserveregs(fs, 1)
		end
		self:forbody(ls, base, line, 1, true)
	end

	------------------------------------------------------------------------
	-- parse a generic for loop, calls forbody()
	-- * used in forstat()
	------------------------------------------------------------------------
	function luaY:forlist(ls, indexname)
		-- forlist -> NAME {,NAME} IN explist1 forbody
		local fs = ls.fs
		local e = {}  -- expdesc
		local nvars = 0
		local base = fs.freereg
		-- create control variables
		self:new_localvarliteral(ls, "(for generator)", nvars)
		nvars = nvars + 1
		self:new_localvarliteral(ls, "(for state)", nvars)
		nvars = nvars + 1
		self:new_localvarliteral(ls, "(for control)", nvars)
		nvars = nvars + 1
		-- create declared variables
		self:new_localvar(ls, indexname, nvars)
		nvars = nvars + 1
		while self:testnext(ls, ",") do
			self:new_localvar(ls, self:str_checkname(ls), nvars)
			nvars = nvars + 1
		end
		self:checknext(ls, "TK_IN")
		local line = ls.linenumber
		self:adjust_assign(ls, 3, self:explist1(ls, e), e)
		luaK:checkstack(fs, 3)  -- extra space to call generator
		self:forbody(ls, base, line, nvars - 3, false)
	end

	------------------------------------------------------------------------
	-- initial parsing for a for loop, calls fornum() or forlist()
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:forstat(ls, line)
		-- forstat -> FOR (fornum | forlist) END
		local fs = ls.fs
		local bl = {}  -- BlockCnt
		self:enterblock(fs, bl, true)  -- scope for loop and control variables
		luaX:next(ls)  -- skip `for'
		local varname = self:str_checkname(ls)  -- first variable name
		local c = ls.t.token
		if c == "=" then
			self:fornum(ls, varname, line)
		elseif c == "," or c == "TK_IN" then
			self:forlist(ls, varname)
		else
			luaX:syntaxerror(ls, self:LUA_QL("=").." or "..self:LUA_QL("in").." expected")
		end
		self:check_match(ls, "TK_END", "TK_FOR", line)
		self:leaveblock(fs)  -- loop scope (`break' jumps to this point)
	end

	------------------------------------------------------------------------
	-- parse part of an if control structure, including the condition
	-- * used in ifstat()
	------------------------------------------------------------------------
	function luaY:test_then_block(ls)
		-- test_then_block -> [IF | ELSEIF] cond THEN block
		luaX:next(ls)  -- skip IF or ELSEIF
		local condexit = self:cond(ls)
		self:checknext(ls, "TK_THEN")
		self:block(ls)  -- `then' part
		return condexit
	end

	------------------------------------------------------------------------
	-- parse an if control structure
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:ifstat(ls, line)
		-- ifstat -> IF cond THEN block {ELSEIF cond THEN block} [ELSE block] END
		local fs = ls.fs
		local escapelist = luaK.NO_JUMP
		local flist = self:test_then_block(ls)  -- IF cond THEN block
		while ls.t.token == "TK_ELSEIF" do
			escapelist = luaK:concat(fs, escapelist, luaK:jump(fs))
			luaK:patchtohere(fs, flist)
			flist = self:test_then_block(ls)  -- ELSEIF cond THEN block
		end
		if ls.t.token == "TK_ELSE" then
			escapelist = luaK:concat(fs, escapelist, luaK:jump(fs))
			luaK:patchtohere(fs, flist)
			luaX:next(ls)  -- skip ELSE (after patch, for correct line info)
			self:block(ls)  -- 'else' part
		else
			escapelist = luaK:concat(fs, escapelist, flist)
		end
		luaK:patchtohere(fs, escapelist)
		self:check_match(ls, "TK_END", "TK_IF", line)
	end

	------------------------------------------------------------------------
	-- parse a local function statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:localfunc(ls)
		local v, b = {}, {}  -- expdesc
		local fs = ls.fs
		self:new_localvar(ls, self:str_checkname(ls), 0)
		self:init_exp(v, "VLOCAL", fs.freereg)
		luaK:reserveregs(fs, 1)
		self:adjustlocalvars(ls, 1)
		self:body(ls, b, false, ls.linenumber)
		luaK:storevar(fs, v, b)
		-- debug information will only see the variable after this point!
		self:getlocvar(fs, fs.nactvar - 1).startpc = fs.pc
	end

	------------------------------------------------------------------------
	-- parse a local variable declaration statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:localstat(ls)
		-- stat -> LOCAL NAME {',' NAME} ['=' explist1]
		local nvars = 0
		local nexps
		local e = {}  -- expdesc
		repeat
			self:new_localvar(ls, self:str_checkname(ls), nvars)
			nvars = nvars + 1
		until not self:testnext(ls, ",")
		if self:testnext(ls, "=") then
			nexps = self:explist1(ls, e)
		else
			e.k = "VVOID"
			nexps = 0
		end
		self:adjust_assign(ls, nvars, nexps, e)
		self:adjustlocalvars(ls, nvars)
	end

	------------------------------------------------------------------------
	-- parse a function name specification
	-- * used in funcstat()
	------------------------------------------------------------------------
	function luaY:funcname(ls, v)
		-- funcname -> NAME {field} [':' NAME]
		local needself = false
		self:singlevar(ls, v)
		while ls.t.token == "." do
			self:field(ls, v)
		end
		if ls.t.token == ":" then
			needself = true
			self:field(ls, v)
		end
		return needself
	end

	------------------------------------------------------------------------
	-- parse a function statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:funcstat(ls, line)
		-- funcstat -> FUNCTION funcname body
		local v, b = {}, {}  -- expdesc
		luaX:next(ls)  -- skip FUNCTION
		local needself = self:funcname(ls, v)
		self:body(ls, b, needself, line)
		luaK:storevar(ls.fs, v, b)
		luaK:fixline(ls.fs, line)  -- definition 'happens' in the first line
	end

	------------------------------------------------------------------------
	-- parse a function call with no returns or an assignment statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:exprstat(ls)
		-- stat -> func | assignment
		local fs = ls.fs
		local v = {}  -- LHS_assign
					v.v = {}
		self:primaryexp(ls, v.v)
		if v.v.k == "VCALL" then  -- stat -> func
			luaP:SETARG_C(luaK:getcode(fs, v.v), 1)  -- call statement uses no results
		else  -- stat -> assignment
			v.prev = nil
			self:assignment(ls, v, 1)
		end
	end

	------------------------------------------------------------------------
	-- parse a return statement
	-- * used in statements()
	------------------------------------------------------------------------
	function luaY:retstat(ls)
		-- stat -> RETURN explist
		local fs = ls.fs
		local e = {}  -- expdesc
		local first, nret  -- registers with returned values
		luaX:next(ls)  -- skip RETURN
		if self:block_follow(ls.t.token) or ls.t.token == ";" then
			first, nret = 0, 0  -- return no values
		else
			nret = self:explist1(ls, e)  -- optional return values
			if self:hasmultret(e.k) then
				luaK:setmultret(fs, e)
				if e.k == "VCALL" and nret == 1 then  -- tail call?
					luaP:SET_OPCODE(luaK:getcode(fs, e), "OP_TAILCALL")
					lua_assert(luaP:GETARG_A(luaK:getcode(fs, e)) == fs.nactvar)
				end
				first = fs.nactvar
				nret = self.LUA_MULTRET  -- return all values
			else
				if nret == 1 then  -- only one single value?
					first = luaK:exp2anyreg(fs, e)
				else
					luaK:exp2nextreg(fs, e)  -- values must go to the 'stack'
					first = fs.nactvar  -- return all 'active' values
					lua_assert(nret == fs.freereg - first)
				end
			end--if
		end--if
		luaK:ret(fs, first, nret)
	end

	------------------------------------------------------------------------
	-- initial parsing for statements, calls a lot of functions
	-- * returns boolean instead of 0|1
	-- * used in chunk()
	------------------------------------------------------------------------
	function luaY:statement(ls)
		local line = ls.linenumber  -- may be needed for error messages
		local c = ls.t.token
		if c == "TK_IF" then  -- stat -> ifstat
			self:ifstat(ls, line)
			return false
		elseif c == "TK_WHILE" then  -- stat -> whilestat
			self:whilestat(ls, line)
			return false
		elseif c == "TK_DO" then  -- stat -> DO block END
			luaX:next(ls)  -- skip DO
			self:block(ls)
			self:check_match(ls, "TK_END", "TK_DO", line)
			return false
		elseif c == "TK_FOR" then  -- stat -> forstat
			self:forstat(ls, line)
			return false
		elseif c == "TK_REPEAT" then  -- stat -> repeatstat
			self:repeatstat(ls, line)
			return false
		elseif c == "TK_FUNCTION" then  -- stat -> funcstat
			self:funcstat(ls, line)
			return false
		elseif c == "TK_LOCAL" then  -- stat -> localstat
			luaX:next(ls)  -- skip LOCAL
			if self:testnext(ls, "TK_FUNCTION") then  -- local function?
				self:localfunc(ls)
			else
				self:localstat(ls)
			end
			return false
		elseif c == "TK_RETURN" then  -- stat -> retstat
			self:retstat(ls)
			return true  -- must be last statement
		elseif c == "TK_BREAK" then  -- stat -> breakstat
			luaX:next(ls)  -- skip BREAK
			self:breakstat(ls)
			return true  -- must be last statement
		else
			self:exprstat(ls)
			return false  -- to avoid warnings
		end--if c
	end

	------------------------------------------------------------------------
	-- parse a chunk, which consists of a bunch of statements
	-- * used in parser(), body(), block(), repeatstat()
	------------------------------------------------------------------------
	function luaY:chunk(ls)
		-- chunk -> { stat [';'] }
		local islast = false
		self:enterlevel(ls)
		while not islast and not self:block_follow(ls.t.token) do
			islast = self:statement(ls)
			self:testnext(ls, ";")
			lua_assert(ls.fs.f.maxstacksize >= ls.fs.freereg and
								 ls.fs.freereg >= ls.fs.nactvar)
			ls.fs.freereg = ls.fs.nactvar  -- free registers
		end
		self:leavelevel(ls)
	end

	-- }======================================================================





	luaX:init()  -- required by llex
	local LuaState = {}  -- dummy, not actually used, but retained since the intention is to complete a straight port

	------------------------------------------------------------------------
	-- interfacing to yueliang
	------------------------------------------------------------------------

	Compile = function(source, name)
		name = name or 'compiled-lua';

		local Zio = Z:Init(Z:MakeGetF(source), nil);

		local __function = Y:Parser(LuaState, zio, nil, "@" .. name);
		
		local Writer, Buff = U:MakeSetS();
		
		U:Dump(LuaState, __function, Writer, Buff);

		return Buff.Data;
	end;
end;

return compile;
