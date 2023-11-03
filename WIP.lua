-- 8ch_32bit

-- Important: I WAS NOT THE ORIGINAL AUTHOR OF THIS PROGRAM! This was originally written by Kein-Hong Man (khman@users.sf.net),
-- original credit goes to him and any other contributers. This program has been improved both performance wise, and syntax wise.

local Lua = {}; -- Main port module to interact with the system

local Z = {}; -- Input reader module (Unused as all Z functions are locally defined (e.g. function: Z_MakeStringReader))
local X = {}; -- Lexer module
local P = {}; -- Instruction module
local Y = {}; -- Parser module
local K = {}; -- Code generator module
local U = {}; -- String dumper module

--//----------------------------------------//--
--* Module Dependencies
--//----------------------------------------//--

local NIL = nil;

local LexerTokens = {};
local LexerEnums  = {};

local Inf = 1 / 0;
local NaN = 0 / 0;

local SizeSizeT   = 8; -- Size of size_t (strings) in bytes
local ShortMax    = 32767; -- Max short int size
local MaxVars     = 200; -- Max variable amount
local MaxUpvalues = 60; -- Max upvalue amount
local MaxInt      = 2147483645; -- Max integer size
local MaxCCalls   = 200; -- Maximum calls that would be called in a C stack

local FieldsPerFlush = 50;

local HasArgMask     = 2;
local VarargHasArg   = 1;
local VarargIsVararg = 2;
local VarargNeedsarg = 4;

local MultipleReturn = -1;

local MaxStack = 250; -- Max amount a stack can be allocated

local EOZ    = "EOZ"; -- End of stream
local Vararg = "..."; -- Vararg string

local Char0 = "\0";

local BufferSize = 512; -- Buffer size

local MaxSource = 80; -- max source size
local LuaQs     = "'%s'"; -- Not used, but a template for whats used 
local LuaLStr   = 1;

local InstrString = "MOVE LOADK LOADBOOL LOADNIL GETUPVAL GETGLOBAL GETTABLE SETGLOBAL SETUPVAL SETTABLE NEWTABLE SELF ADD SUB MUL DIV MOD POW UNM NOT LEN CONCAT JMP EQ LT LE TEST TESTSET CALL TAILCALL RETURN FORLOOP FORPREP TFORLOOP SETLIST CLOSE CLOSURE VARARG";
local Reserved    = "TK_AND and TK_BREAK break TK_DO do TK_ELSE else TK_ELSEIF elseif TK_END end TK_FALSE false TK_FOR for TK_FUNCTION function TK_IF if TK_IN in TK_LOCAL local TK_NIL nil TK_NOT not TK_OR or TK_REPEAT repeat TK_RETURN return TK_THEN then TK_TRUE true TK_UNTIL until TK_WHILE while TK_CONCAT .. TK_DOTS ... TK_EQ == TK_GE >= TK_LE <= TK_NE ~= TK_NAME <name> TK_NUMBER <number> TK_STRING <string> TK_EOS <eof>";

local OpMode = { iABC = 0, iABx = 1, iAsBx = 2 };

local SIZE_A  = 8;
local SIZE_B  = 9;
local SIZE_C  = 9;
local SIZE_Bx = 18;

local SIZE_OP = 6;
local POS_OP  = 0;

local POS_A  = POS_OP + SIZE_OP;
local POS_C  = POS_A  + SIZE_A;
local POS_B  = POS_C  + SIZE_C;
local POS_Bx = POS_C;

local MAXARG_Bx  = 262143;
local MAXARG_sBx = 131071;

local MAXARG_A = 255;
local MAXARG_B = 511;
local MAXARG_C = 511;

local BitRK      = 256;
local MaxIndexRK = 255;

local NO_REG = MAXARG_A;

local Amount  = 0;
local OpCode  = {};
local OpNames = {};
local ROpCode = {};
local OpModes = {};

local OpArgMask = { OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3 };

--//----------------------------------------//--
--* Define Libraries
--//----------------------------------------//--

local io = io;
local type = type;
local typeof = typeof or type; -- Can be nil (LuaU only)
local bit = bit; -- Can be nil (LuaJIT only)
local bit32 = bit32 or bit; -- Can be nil (Lua 5.2 only)
local string = string;
local math = math;
local table = table;

local Abs   = math.abs;
local Min   = math.min;
local Log   = math.log;
local Floor = math.floor;

local Open = io.open;

local Insert = table.insert;

local Sub    = string.sub;
local Byte   = string.byte;
local Char   = string.char;
local Find   = string.find;
local Lower  = string.lower;
local Format = string.format;
local Gmatch = string.gmatch;

--//----------------------------------------//--
--* String functions
--//----------------------------------------//--

local Split = string.split or function(String, Seperator) -- string.split is implemented into LuaU
	local Substrings = {};

	if not Seperator then -- Common to only split by spaces
		for Substr in Gmatch(String, "%S+") do
			Insert(Substrings, Substr);
		end;

		return Substrings;
	end;

	for Substr in Gmatch(String, "([^" .. Seperator .. "]+)") do
		Insert(Substrings, Substr);
	end;

	return Substrings;
end;

--//----------------------------------------//--
--* Math functions
--//----------------------------------------//--

local Ldexp = math.ldexp or function(Mantissa, Exponent)
    return Mantissa * (2 ^ Exponent);
end;

local Frexp = math.frexp or function(x)
	local Mantissa, Exponent = 0, 0;

	if x == 0 then return Mantissa, Exponent; end;
		
	local IsNegative = x < 0;
	local New = Abs(x);

	Exponent = Floor(Log(New, 2)) + 1;
	Mantissa = New / (2 ^ Exponent);
		
	if Abs(Mantissa) >= 1 then
		Mantissa = Mantissa / 2;
	end;
		
	if IsNegative then
		return -Mantissa, Exponent;
	end;

	return Mantissa, Exponent;
end;

--//----------------------------------------//--
--* Bitwise functions (credit to Ekdohibs for
--* original function)
--//----------------------------------------//--

local Bor = bit32.bor or function(ArgA, ArgB)
	if ArgB == 255 then
		return (ArgA - (ArgA % 256)) + 255;
	end;

	if ArgB == 65535 then
		return (ArgA - (ArgA % 65536)) + 65535;
	end;

	if ArgB == 4294967295 then
		return 4294967295;
	end;
	
	local Return = 0;
	local _P     = 1;

	ArgA, ArgB = ArgA % 4294967296, ArgB % 4294967296;

	for _ = 1, 32 do
		local A = ArgA % 2;
		local B = ArgB % 2;
		
		ArgA = ArgA / 2;
		ArgA = ArgA - (ArgA % 1);
		ArgB = ArgB / 2;
		ArgB = ArgB - (ArgB % 1);

		if A + B == 2 then
			Return = Return + _P;
		end;

		_P = _P * 2;
	end;

	return Return;
end;

--//----------------------------------------//--
--* Other functions used
--//----------------------------------------//--

local function CharIsNewLine(x)
	return x == "\n" or x == "\r";
end;

local function lua_Assert(Value, Message) -- Simpler assertion function
	return Value or error(Message or "assertion failed!");
end;

local function Opmode(T, A, B, C, __OpMode)
	local OpArgMaskB = OpArgMask[B];
	local OpArgMaskC = (B == C and OpArgMaskB) or OpArgMask[C]; -- Reduces table indexes

	return Bor(Bor(T * 128, A * 64) + Bor(OpArgMaskB * 16, OpArgMaskC * 4), P.OpMode[__OpMode] + 4);
end;

local function Z_MakeStringReader(Buff)
	return function() -- chunk reader anonymous function here
		if not Buff then
			return;
		end;

		local Data = Buff; Buff = nil;

		return Data;
	end;
end;

local function Z_MakeFileReader(Source)
	local Position  = 1;
	local Length    = #Source;
	local BuffSize1 = BufferSize - 1;

	return function() -- chunk reader anonymous function here
		local Buff = Sub(Source, Position, Position + BuffSize1); -- Use string.sub() instead of :sub()
		Position = Min(Length + 1, Position + BufferSize);

		return Buff;
	end;
end;

local function Z_Init(Reader, Data)
	if not Reader then
		return;
	end;

	Data = Data or "";

	return { Reader = Reader, Data = Data, P = 0, N = #Data };
end;

local function Z_Fill(Zio)
	local Buff = Zio.Reader();

	Zio.Data = Buff;

	if not Buff or Buff == "" then
		return EOZ;
	end;

	Zio.P = 1;
	Zio.N = #Buff - 1;

	return Sub(Buff, 1, 1);
end;

local function Z_GetChar(Zio)
	local N  = Zio.N;
	local _P = Zio.P + 1;

	if N > 0 then
		Zio.N = N - 1;
		Zio.P = _P;

		return Sub(Zio.Data, _P, _P);
	end;

	return Z_Fill(Zio);
end;

------------------------------------------------------------------------
-- returns a suitably-formatted chunk name or id
-- * from lobject.c, used in llex.c and ldebug.c
-- * the result, out, is returned (was first argument)
------------------------------------------------------------------------
function X:GetChunkID(Source, BuffLength)
	local Output = "";
	local First  = Sub(Source, 1, 1);

	if First == "=" then
		return Sub(Source, 2, BuffLength);  -- remove first char
	end;

	local Length = #Source;

	if First == "@" then
		Source = Sub(Source, 2);  -- skip the '@'
			
		BuffLength = BuffLength - 8; -- bufflen = bufflen - #(" '...' ");

		if Length > BuffLength then
			Source = Sub(Source, (Length - BuffLength) + 1);  -- get last part of file name
			Output = Output .. Vararg;
		end;

		Output = Output .. Source;
	else
		local Len = Find(Source, "[\n\r]");  -- stop at first newline

		Len = Len and Len - 1 or Length;
		Len = Len > BuffLength and BuffLength or Len;

		BuffLength = BuffLength - #(" [string \"...\"] ");

		Output = "[string \"";

		local Value = Source;

		if Len < Length then  -- must truncate?
			Value = Sub(Source, 1, Len) .. Vararg;
		end;

		Output = Output .. Value .. "\"]";
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
function X:Token2Str(Token)
	if Sub(Token, 1, 3) ~= "TK_" then
		if Find(Token, "%c") then
			return Format("char(%d)", Byte(Token));
		end;

		return Token;
	end;

	return self.Tokens[Token];
end;

function X:TextToken(LexerState, Token)
	if Token == "TK_NAME" or Token == "TK_STRING" or Token == "TK_NUMBER" then
		return LexerState.Buff;
	end;

	if Sub(Token, 1, 3) ~= "TK_" then
		if Find(Token, "%c") then
			return Format("char(%d)", Byte(Token));
		end;

		return Token;
	end;

	return self.Tokens[Token];
end;

------------------------------------------------------------------------
-- throws a lexer error
-- * txtToken has been made local to luaX:lexerror
-- * can't communicate LUA_ERRSYNTAX, so it is unimplemented
------------------------------------------------------------------------
function X:LexError(LexerState, Message, Token)
	if Token then
		error(Format("%s near '%s'", Message, self:TextToken(LexerState, Token)), 0)
	end;
	
	error(Format("%s:%d: %s", self:ChunkID(LexerState.Source, MaxSource), LexerState.LineNumber, Message), 0);
end;

------------------------------------------------------------------------
-- throws a syntax error (mainly called by parser)
-- * ls.t.token has to be set by the function calling luaX:llex
--   (see luaX:next and luaX:lookahead elsewhere in this file)
------------------------------------------------------------------------
function X:SyntaxError(LexerState, Message)
	error(Format("%s near '%s'", Message, self:TextToken(LexerState, LexerState.T.Token)), 0);
end;

------------------------------------------------------------------------
-- move on to next line
------------------------------------------------------------------------

function X:InclineNumber(LexerState)
	local Old = LexerState.Current;
	
	self:NextChar(LexerState);

	local New = LexerState.Current;

	if CharIsNewLine(New) and New ~= Old then
		self:NextChar(LexerState);
	end;

	local LineNumber = LexerState.LineNumber + 1;

	LexerState.LineNumber = LineNumber;

	if LineNumber >= MaxInt then
		error(Format("%s near '%s'", "chunk has too many lines", self:TextToken(LexerState, LexerState.T.Token)), 0);
	end;
end;

------------------------------------------------------------------------
-- initializes an input stream for lexing
-- * if ls (the lexer state) is passed as a table, then it is filled in,
--   otherwise it has to be retrieved as a return value
-- * LUA_MINBUFFER not used; buffer handling not required any more
------------------------------------------------------------------------
function X:SetInput(LuaState, LexerState, Zio, Source) 
	LexerState = LexerState or {}; -- create struct

	LexerState.LookAhead = LexerState.LookAhead or {};
	LexerState.Tokens    = LexerState.T or {};

	LexerState.DecPoint = ".";

	LexerState.LuaState  = LuaState;
	LexerState.Zio       = Zio;

	LexerState.FunctionState = nil;

	LexerState.LineNumber = 1;
	LexerState.LastLine   = 1;

	LexerState.Source = Source;

	LexerState.Lookahead.Token = "TK_EOS";  -- no look-ahead token

	self:NextChar(LexerState);  -- read first char
end;

--[[--------------------------------------------------------------------
-- LEXICAL ANALYZER
----------------------------------------------------------------------]]

------------------------------------------------------------------------
-- checks if current character read is found in the set 'set'
------------------------------------------------------------------------
function X:CheckNext(LexerState, Set)
	local Value = Find(Set, LexerState.Current, 1) ~= nil;

	if Value then
		self:SaveAndNext(LexerState);
	end;

	return Value;
end;

------------------------------------------------------------------------
-- retrieve next token, checking the lookahead buffer if necessary
-- * note that the macro next(ls) in llex.c is now luaX:nextc
-- * utilized used in lparser.c (various places)
------------------------------------------------------------------------
function X:Next(LexerState)
	LexerState.LastLine = LexerState.LineNumber;

	local T         = LexerState.T;
	local LookAhead = LexerState.LookAhead;

	local Token = LookAhead.Token;

	if Token == "TK_EOS" then  -- is there a look-ahead token?
		LookAhead.Token = self:Lexer(LexerState, T);  -- read next token
	else
		T.SemInfo = LookAhead.SemInfo;  -- use this one
		T.Token   = Token;

		LookAhead.Token = "TK_EOS";  -- and discharge it
	end;
end;

------------------------------------------------------------------------
-- fill in the lookahead buffer
-- * utilized used in lparser.c:constructor
------------------------------------------------------------------------
function X:LookAhead(LexerState)
	local Lookahead = LexerState.Lookahead;

	Lookahead.Token = self:Lexer(LexerState, Lookahead);
end;

------------------------------------------------------------------------
-- gets the next character and returns it
-- * this is the next() macro in llex.c; see notes at the beginning
------------------------------------------------------------------------
function X:NextChar(LexerState)
	local C = Z:GetChar(LexerState.Z);
	LexerState.Current = C;

	return C;
end

------------------------------------------------------------------------
-- saves the given character into the token buffer
-- * buffer handling code removed, not used in this implementation
-- * test for maximum token buffer length not used, makes things faster
------------------------------------------------------------------------

function X:Save(LexerState, _Char)
	LexerState.Buff = LexerState.Buff .. _Char;
end;

------------------------------------------------------------------------
-- save current character into token buffer, grabs next character
-- * like luaX:nextc, returns the character read for convenience
------------------------------------------------------------------------
function X:SaveAndNext(LexerState)
	LexerState.Buff = LexerState.Buff .. LexerState.Current;

	return self:NextChar(LexerState);
end;

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
function X:str2d(String)
	local Result = tonumber(String);

	if Result then
		return Result;
	end;
	
	if Lower(Sub(String, 1, 2)) == "0x" then  -- maybe an hexadecimal constant?
		Result = tonumber(String, 16);

		if Result then
			return Result;
		end;
	end;
end;

------------------------------------------------------------------------
-- single-character replacement, for locale-aware decimal points
------------------------------------------------------------------------
function X:buffreplace(LexerState, From, To)
	local Result, Buff = "", LexerState.Buff;
	local Length = #Buff;

	for Position = 1, Length do
		local C = Sub(Buff, Position, Position);

		if C == From then
			C = To;
		end;

		Result = Result .. C;
	end;

	LexerState.Buff = Result;
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

	self:buffreplace(lexState, ".", lexState.DecPoint);  -- follow locale for decimal point
	
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

		if C == EOZ then
			self:lexerror(lexState, token and "unfinished long string" or "unfinished long comment", "TK_EOS");
		elseif C == "[" then
			if self.LuaLStr then
				if self:skip_sep(lexState) == seperator then
					self:save_and_next(lexState);  -- skip 2nd '['

					Count = Count + 1;

					if self.LuaLStr == 1 then
						if seperator == 0 then
							self:lexerror(lexState, "nesting of [[...]] is deprecated", "[")
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

		if C == EOZ then
			self:lexerror(lexState, "unfinished string", "TK_EOS");
		elseif self:currIsNewline(lexState) then
			self:lexerror(lexState, "unfinished string", "TK_STRING");
		end;

		if C == "\\" then
			C = self:nextc(lexState);  -- do not save the '\'

			if self:currIsNewline(lexState) then
				self:save(lexState, "\n");
				self:inclinenumber(lexState);
			elseif C ~= EOZ then
				local I = Find("abfnrtv", C, 1);

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

						I = I + 1;
					until I >= 3 or not Find(lexState.Current, "%d");

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
function P:CREATE_Inst(Number)
	local OP_Code = (Number % 64);
	local OP_Base = (Number - OP_Code) / 64;
	local OP_A    = (OP_Base % 256);

	return { OP = OP_Code, A = OP_A, Bx = (OP_Base - OP_A) / 256 };
end;

------------------------------------------------------------------------
-- returns a 4-char string little-endian encoded form of an instruction
------------------------------------------------------------------------
function P:Instruction(Instruction)
	local OP_Code = Instruction.OP;
	local OP_A    = Instruction.A;
	local OP_B    = Instruction.B;  -- Can be nil
	local OP_Bx   = Instruction.Bx; -- Can be nil
	local OP_C    = Instruction.C;  -- Can be nil
	
	if OP_Bx then -- change to OP/A/B/C format
		Instruction.C = (OP_Bx % 512);
		Instruction.B = (OP_Bx - OP_C) / 512;
	end;
	
	local BaseNumber = OP_A * 64 + OP_Code;

	local Char1 = BaseNumber % 256;
	local Char2 = OP_C * 64  + (BaseNumber - Char1) / 256;
	local Char3 = OP_B * 128 + (BaseNumber - Char2) / 256;
	local Char4 = (BaseNumber - Char3) / 256;
	
	return Char(Char1, Char2, Char3, Char4);
end;

------------------------------------------------------------------------
-- decodes a 4-char little-endian string into an instruction struct
------------------------------------------------------------------------
function P:DecodeInst(String)
	local BaseNumber = Byte(String, 1);

	local OP_Code = BaseNumber % 64;
	local OP_A    = (Byte(String, 2) * 4 + (BaseNumber - OP_Code) / 64) % 256;
	local OP_C    = (Byte(String, 3) * 4 + (BaseNumber - OP_A)) / 256;
	local OP_B    = (Byte(String, 4) * 2 + (BaseNumber - OP_C)) / 512;

	local Instr = {};

	Instr.OP = OP_Code;
	Instr.A  = OP_A;
	Instr.C  = OP_C;
	
	if OpMode[tonumber(Sub(OpModes[OP_Code], 7, 7))] ~= "iABC" then
		Instr.Bx = OP_B * 512 + OP_C;
	else
		Instr.B  = OP_B;
	end;
	
	return Instr;
end;

-- test whether value is a constant
function P:IsK(x)
	return x >= BitRK;
end;

-- gets the index of the constant
function P:IndexK(x)
	return x - BitRK;
end;

-- code a constant index as a RK value
function P:RKAsk(x)
	return x + BitRK;
end;

------------------------------------------------------------------------
-- e.g. to compare with symbols, luaP:getOpMode(...) == luaP.OpCode.iABC
-- * accepts opcode parameter as strings, e.g. "OP_MOVE"
------------------------------------------------------------------------

function P:GetOpMode(m)
	return OpModes[OpCode[m]] % 4;
end;

function P:GetBMode(m)
	return (OpModes[OpCode[m]] / 16) % 4;
end;

function P:GetCMode(m)
	return (OpModes[OpCode[m]] / 4) % 4;
end;

function P:TestAMode(m)
	return (OpModes[OpCode[m]] / 64) % 2;
end;

function P:TestTMode(m)
	return OpModes[OpCode[m]] / 128;
end;

local U_DumpFunction, U_Dump;

local function U_MakeStringSet()
	return function(String, Buff)  -- chunk writer
		if not String then
			return 0;
		end;
		
		Buff.Data = Buff.Data .. String;
		
		return 1;
	end, { Data = "" };
end;

local function U_MakeFileSet(fileName)
	local Buff = {};
	local Port = Open(fileName, "wb");
	
	if not Port then
		return;
	end;

	Buff.H = Port;
	
	return function(String, Buff)  -- chunk writer
		local H = Buff.H;
		
		if not H then
			return 0;
		end;
		
		if not String then
			if H:close() then
				return 0;
			end;
		else
			if H:write(String) then
				return 0;
			end;
		end;
		
		return 1;
	end, Buff;
end;

local function U_FromDouble(x)
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
		Mantissa = 4294967296 * (Mantissa * 2) - 1;
		Exponent = Exponent + 1022;
	end;
	
	local Val = "";
	
	local New = Floor(Mantissa);
	
	for _ = 1, 6 do
		local __Byte = Char(New % 256);
		
		Val = Val .. __Byte; -- 47:0
	end;
	
	Val = Val .. Char(((Exponent * 16) + New) % 256); -- 55:48
	Val = Val .. Char(((Sign * 128) + New) % 256); -- 63:56

	return Val;
end;

local function U_FromInt(x)
	local Val = "";

	x = Floor(x);
	x = x < 0 and 4294967296 + x or x;
	
	for _ = 1, 4 do
		Val = Val .. Char(x % 256);

		x = x / 256;
		x = x - (x % 1);
	end;
	
	return Val;
end;

local function U_DumpBlock(Buff, D)
	if D.Status == 1 then
		return;
	end;

	D.Status = D.Write(Buff, D.Data);
end;

local function U_DumpChar(__Char, D)
	U_DumpBlock(Char(__Char), D);
end;

local function U_DumpInt(x, D)
	U_DumpBlock(U_FromInt(x), D);
end;

local function U_DumpSizeT(x, D)
	U_DumpBlock(U_FromInt(x), D);
	
	if SizeSizeT == 8 then
		U_DumpBlock(U_FromInt(0), D);
	end;
end;

local function U_DumpNumber(x, D)
	U_DumpBlock(U_FromDouble(x), D);
end;

local function U_DumpString(String, D)
	if not String then
		return U_DumpSizeT(0, D);
	end;

	String = String .. Char0;
	
	U_DumpSizeT(#String, D);
	U_DumpBlock(String, D);
end;

local function U_DumpCode(Instr, D)
	local Size = Instr.SizeCode;
	local Code = Instr.Code;
	
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		U_DumpBlock(P:Instruction(Code[Index]), D);
	end;
end;

local function U_DumpConstants(Const, D)
	local Source = Const.Source;
	local Size   = Const.SizeConst;

	local _K, _P = Const.K, Const.P;
		
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		local Object = K[Index];
		local Value  = Object.Value;

		local Type = typeof(Value);
		
		if Type == "boolean" then
			U_DumpChar(Type, LUA_TBOOLEAN);
			U_DumpChar(Value and 1 or 0, D);
		elseif Type == "number" then
			U_DumpChar(Type, LUA_TNUMBER);
			U_DumpNumber(Value, D);
		elseif Type == "string" then
			U_DumpChar(Type, LUA_TSTRING);
			U_DumpString(Value, D);
		else
			U_DumpChar(Type, LUA_TNIL);
		end;
	end;
	
	Size = Const.SizeP;
	
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		U_DumpFunction(P[Index], Source, D);
	end;
end;

local function U_DumpDebug(Debug, D)
	local Size     = D.Strip and 0 or Debug.SizeLineInfo; -- dump line information
	local LineInfo = Debug.LineInfo;
	local LocVars  = Debug.LocVars;
	local Upvalues = Debug.Upvalues;
	
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		U_DumpInt(LineInfo[Index], D);
	end;
	
	Size = D.Strip and 0 or Debug.SizeLocVars; -- dump local information
	
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		local Var = LocVars[Index];
		
		U_DumpString(Var.VarName, D);
		U_DumpInt(Var.StartPC, D);
		U_DumpInt(Var.EndPC, D);
	end;
	
	Size = D.Strip and 0 or Debug.SizeUpvalues; -- dump upvalue information
	
	U_DumpInt(Size, D);
	
	for Index = 0, Size - 1 do
		U_DumpString(Upvalues[Index], D);
	end;
end;

function U_DumpFunction(Function, _P, D)
	local Source = Function.Source;
	
	if Source == _P or D.Strip then
		Source = _P;
	end;
	
	U_DumpString(Source, D);
	U_DumpInt(Function.lineDefined, D);
	U_DumpInt(Function.lastlinedefined, D);
	U_DumpChar(Function.nups, D);
	U_DumpChar(Function.numparams, D);
	U_DumpChar(Function.is_vararg, D);
	U_DumpChar(Function.maxstacksize, D);

	U_DumpCode(Function, D);
	U_DumpConstants(Function, D);
	U_DumpDebug(Function, D);
end;

local Header = "\27Lua\81\0\1\4" .. Char(SizeSizeT) .. "\4\8\0";

function U_Dump(LuaState, Function, Writer, Data, Strip)
	local DumpState = {};  -- DumpState

	DumpState.LuaState = LuaState;
	DumpState.Write    = Writer;
	DumpState.Data     = Data;
	DumpState.Strip    = Strip;
	DumpState.Status   = 0;
	
	U_DumpBlock(Header, DumpState);
	U_DumpFunction(Function, nil, DumpState);
	
	DumpState.Write(nil, Data);
	
	return DumpState.Status;
end;

function K.Set(Object, x)
	Object.Value = x;
end;

function K.SetNil(Object)
	Object.Value = nil;
end;

K.SetNValue = K.Set;
K.SetHValue = K.Set;
K.SetBValue = K.Set;

local NO_JUMP = -1;

local OperatorTree = {
	OPR_ADD = 0, OPR_SUB = 1, OPR_MUL = 2, OPR_DIV = 3, OPR_MOD = 4, OPR_POW = 5,
	OPR_CONCAT = 6,
	OPR_NE = 7, OPR_EQ = 8,
	OPR_LT = 9, OPR_LE = 10, OPR_GT = 11, OPR_GE = 12,
	OPR_AND = 13, OPR_OR = 14,
	OPR_NOBINOPR = 15,
};

local UnaryIperatorTree = {
	OPR_MINUS = 0, OPR_NOT = 1, OPR_LEN = 2, OPR_NOUNOPR = 3,
};

function K.GetCode(FunctionState, Expression)
	return FunctionState.F.Code[Expression.Info];
end;

function K:CodeAsBx(fs, o, A, sBx)
	return self:CodeABx(fs, o, A, sBx + MAXARG_sBx);
end;


function K:SetMulteReturns(FunctionState, Expression)
	self:SetReturns(FunctionState, Expression, MultipleReturn);
end;

function K:HasJumps(Expression)
	return Expression.T ~= Expression.F;
end;

function K.IsNumeral(Expression)
	return Expression.K == "VKNUM" and Expression.T == NO_JUMP and Expression.F == NO_JUMP;
end;

function K:Nil(FunctionState, From, N)
	local Pc          = FunctionState.Pc;
	local LastTarget  = FunctionState.LastTarget;
	local NactVar     = FunctionState.NactVar;
	local Function    = FunctionState.Function;

	local Code = Function.Code;

	local Value = From + N - 1;
	
	if Pc > LastTarget then  -- no jumps to current position?
		if Pc == 0 then  -- function start?
			if From >= NactVar then	return; end; -- positions are already clean
		end;

		local Previous = Code[Pc - 1];
		
		if P:GET_OPCODE(Previous) == "OP_LOADNIL" then
			local A = Previous.A;
			local B = Previous.B;
			
			if (A <= From) and (From <= B + 1) then  -- can connect both?
				if Value > B then
					Previous.B = Value;
				end;
				
				return;
			end;
		end;
	end;
	
	self:CodeABC(FunctionState, "OP_LOADNIL", From, Value, 0);  -- else no optimization
end;

function K:Jump(FunctionState)
	local Jpc = FunctionState.Jpc;  -- save list of jumps to here
	FunctionState.Jpc = NO_JUMP;
	
	local Instr = self:CodeAsBx(FunctionState, "OP_JMP", 0, NO_JUMP);
	Instr       = self:Concat(FunctionState, Instr, Jpc);
	
	return Instr;
end;

function K:Return(Object, First, NumberOfReturns)
	self:CodeABC(Object, "OP_RETURN", First, NumberOfReturns + 1, 0);
end;

function K:ConditionalJump(FunctionState, ...)
	self:CodeABC(FunctionState, ...);
	
	return self:Jump(FunctionState);
end;

function K.FixJump(FunctionState, Pc, Destination)
	local Function = FunctionState.Function;
	local Code     = Function.Code;
	
	local JMP    = Code[Pc];
	local Offset = Destination - (Pc + 1);
	
	if Abs(Offset) > MAXARG_sBx then
		X:SyntaxError(FunctionState.LexState, "control structure too long");
	end;

	JMP.sBx = Offset;
end;

function K.GetLabel(FunctionState)
	local PC = FunctionState.PC;
	FunctionState.LastTarget = PC;
	
	return PC;
end;

function K.GetJump(FunctionState, Pc)
	local Code   = FunctionState.Function.Code;
	local Offset = Code[Pc].sBx;
	
	if Offset == NO_JUMP then  -- point to itself represents end of list
		return NO_JUMP;  -- end of list
	end;

	return (Pc + 1) + Offset;  -- turn offset into absolute position
end;

function K.GetJumpControl(FunctionState, Pc)
	local Code = FunctionState.Function.Code;
	
	local InstrA = Code[Pc];
	local InstrB = Code[Pc - 1];
	
	if Pc >= 1 then
		if P:TestTMode(P:GET_OPCODE(InstrA)) ~= 0 then return InstrA; end;
	end;

	return InstrB;
end;

function K:NeedValue(FunctionState, List)
	while List ~= NO_JUMP do
		local JumpControl = self.GetJumpControl(FunctionState, List);
		
		if P:GET_OPCODE(JumpControl) ~= "OP_TESTSET" then
			return true;
		end;
		
		List = self.GetJump(FunctionState, List);
	end;
	
	return false;
end;

function K:PatchTestReg(FunctionState, Node, Reg)
	local JMPCtrl      = self.GetJumpControl(FunctionState, Node);
	local JMPCtrl_ArgB = JMPCtrl;
	
	if P:GET_OPCODE(JMPCtrl) ~= "OP_TESTSET" then
		return false; -- cannot patch other instructions
	end;
	
	if Reg ~= NO_REG and Reg ~= JMPCtrl_ArgB then
		JMPCtrl.A = Reg;
	else
		P:SET_OPCODE(JMPCtrl, "OP_TEST");

		JMPCtrl.A = JMPCtrl_ArgB;
		JMPCtrl.B = 0;
	end;
	
	return true;
end

function K:RemoveValues(FunctionState, List)
	while List ~= NO_JUMP do
		self:PatchTestReg(FunctionState, List, NO_REG);
		List = self.GetJump(FunctionState, List);
	end;
end;

function K:PatchListAux(FunctionState, List, VTarget, Reg, DTarget)
	while List ~= NO_JUMP do
		local Next   = self.GetJump(FunctionState, List);
		local Target = (self:PatchTestReg(FunctionState, List, Reg) and VTarget) or DTarget;
		
		self.FixJump(FunctionState, List, Target);
		
		List = Next;
	end;
end;

function K:DischargeJPC(FunctionState)
	local Pc  = FunctionState.Pc;
	local Jpc = FunctionState.Jpc;
	
	self:PatchListAux(FunctionState, Jpc, Pc, NO_REG, Pc);
	
	FunctionState.Jpc = NO_JUMP;
end;

function K:PatchList(FunctionState, List, Target)
	if Target == FunctionState.Pc then
		return self:PatchToHere(FunctionState, List);
	end;

	self:PatchListAux(FunctionState, List, Target, NO_REG, Target);
end;

function K:PatchToHere(FunctionState, List)
	self.GetLabel(FunctionState);

	FunctionState.Jpc = self:Concat(FunctionState, FunctionState.Jpc, List);
end;

function K:Concat(FunctionState, List1, List2)
	local GetJump = self.GetJump;

	if List2 == NO_JUMP then
		return List1;
	end;
	
	if List1 == NO_JUMP then
		return List2;
	end;

	local List = List1;
	local Next = GetJump(FunctionState, List);
		
	while Next ~= NO_JUMP do -- find last element
		List = Next;
		Next = GetJump(FunctionState, List);
	end;
		
	self.FixJump(FunctionState, List, List2);
	
	return List1;
end;

function K.CheckStack(FunctionState, Number)
	local NewStack = FunctionState.FreeReg + Number;
	local Function = FunctionState.Function;
	
	if NewStack > Function.MaxStackSize then
		if NewStack >= MaxStack then
			X:SyntaxError(FunctionState.LexerState, "function or expression too complex")
		end;
		
		Function.MaxStackSize = NewStack;
	end;
end;

function K:ReserveRegs(FunctionState, Number)
	self.CheckStack(FunctionState, Number);
	
	FunctionState.FreeReg = FunctionState.FreeReg + Number;
end;

function K:FreeReg(FunctionState, Reg)
	if not P:IsK(Reg) and Reg >= FunctionState.NactVar then
		FunctionState.FreeReg = FunctionState.FreeReg - 1;
	end;
end;

function K:FreeExpression(FunctionState, Expression)
	if Expression.K == "VNONRELOC" then
		self:FreeReg(FunctionState, Expression.Info);
	end;
end;

function K:AddK(FunctionState, __K, V)
	local Value = __K.Value;
	
	local L  = FunctionState.L;
	local H  = FunctionState.H;
	local _K = FunctionState.K;
	local NK = FunctionState.NK;
	
	local SizeK    = FunctionState.SizeK;
	
	local Idx = H[Value];
	
	if typeof(Idx.Value) == "number" then
		return self:NValue(Idx);
	end;

	Idx = {};
	
	self:SetNValue(Idx, NK);
		
	H[Value] = Idx;
		
	Y:GrowVector(L, _K, NK, SizeK, nil, MAXARG_Bx, "constant table overflow");
		
	_K[NK] = V;
		
	FunctionState.NK = NK + 1;
		
	return NK;
end;

function K:StringK(FunctionState, String)
	local Object = {};
	Object.Value = String;
	
	return self:AddK(FunctionState, Object, Object);
end;

function K:NumberK(FunctionState, Number)
	local Object = {};
	Object.Value = Number;
	
	return self:AddK(FunctionState, Object, Object);
end;

function K:BoolK(FunctionState, Boolean)
	local Object = {};
	Object.Value = Boolean;
	
	return self:AddK(FunctionState, Object, Object);
end;

function K:NilK(FunctionState)
	local _K = {};
	local V  = {};
	
	self:SetNilValue(V)
	self.SetHValue(_K, FunctionState.H);
	
	return self:AddK(FunctionState, _K, V);
end;

function K:SetReturns(FunctionState, Expression, NumberOfResults)
	local _K     = Expression.K;
	local Offset = NumberOfResults + 1;
	local Code   = self.GetCode(FunctionState, Expression);
	
	if _K == "VCALL" then  -- expression is an open function call?
		Code.C = Offset;
	elseif _K == "VVARARG" then
		Code.A = FunctionState.FreeReg;
		Code.B = Offset;
		
		self:ReserveRegs(FunctionState, 1);
	end;
end;

function K:SetOneRet(FunctionState, Expression)
	local _K   = Expression.K;
	local Code = self.GetCode(FunctionState, Expression);
	
	if _K == "VCALL" then  -- expression is an open function call?
		Expression.K    = "VNONRELOC";
		Expression.Info = Code.A;
	elseif _K == "VVARARG" then
		Expression.K = "VRELOCABLE"; -- can relocate its simple result
		Code.B = 2;
	end;
end;

function K:DischargeVars(FunctionState, Expression)
	local _K   = FunctionState.K;
	local Aux  = FunctionState.Aux;
	local Info = FunctionState.Info;
	
	if _K == "VLOCAL" then
		FunctionState.K = "VNONRELOC"
	elseif _K == "VUPVAL" then
		FunctionState.K = "VRELOCABLE";
		FunctionState.Info = self:CodeABC(FunctionState, "OP_GETUPVAL", 0, Info, 0);
	elseif _K == "VGLOBAL" then
		FunctionState.K = "VRELOCABLE";
		FunctionState.info = self:CodeABx(FunctionState, "OP_GETGLOBAL", 0, Info);
	elseif _K == "VINDEXED" then
		FunctionState.K = "VRELOCABLE";
		
		self:FreeReg(FunctionState, Aux);
		self:FreeReg(FunctionState, Info);
		
		Expression.Info = self:CodeABC(FunctionState, "OP_GETTABLE", 0, Info, Aux);
	elseif _K == "VVARARG" or _K == "VCALL" then
		self:SetOneRet(FunctionState, Expression);
	end;
end;

function K:CodeLabel(FunctionState, ...)
	self.GetLabel(FunctionState);
	
	return self:CodeABC(FunctionState, "OP_LOADBOOL", ...);
end

function K:Discharge2Reg(FunctionState, Expression, Reg)
	self:DischargeVars(FunctionState, Expression);

	local _K   = Expression.K;
	local Info = Expression.Info;

	lua_Assert(_K == "VVOID" or _K == "VJMP");

	if _K == "VNIL" then
		self:Nil(FunctionState, Reg, 1)
	elseif _K == "VFALSE" or K == "VTRUE" then
		self:CodeABC(FunctionState, "OP_LOADBOOL", Reg, (K == "VTRUE") and 1 or 0, 0);
	elseif _K == "VK" then
		self:CodeABx(FunctionState, "OP_LOADK", Reg, Info);
	elseif _K == "VKNUM" then
		self:CodeABx(FunctionState, "OP_LOADK", Reg, self:NumberK(FunctionState, Expression.NVal));
	elseif _K == "VRELOCABLE" then
		self.GetCode(FunctionState, Expression).A = Reg;
	elseif K == "VNONRELOC" then
		if Reg ~= Info then self:CodeABC(FunctionState, "OP_MOVE", Reg, Info, 0); end;
	end;
	
	Expression.Info = Reg;
	Expression.K = "VNONRELOC";
end;

function K:Discharge2AnyReg(FunctionState, Expression)
	if Expression.K ~= "VNONRELOC" then
		self:ReserveRegs(FunctionState, 1);
		self:Discharge2Reg(FunctionState, Expression, FunctionState.FreeReg - 1);
	end;
end;

function K:Expression2Reg(FunctionState, Expression, Reg)
	self:Discharge2Reg(FunctionState, Expression, Reg);

	local _K = Expression.K;
	local F  = Expression.F;
	
	if _K == "VJMP" then
		Expression.T = self:Concat(FunctionState, Expression.T, Expression.Info); T = Expression.T;
	end;

	local T = Expression.T;
	
	if self:HasJumps(Expression) then
		local Final; -- position after whole expression
		local PF = -1; -- position of an eventual LOAD false
		local PT = -1; -- position of an eventual LOAD true
		
		if self:NeedValue(FunctionState, T) or self:NeedValue(FunctionState, F) then
			PF = self:CodeLabel(FunctionState, Reg, 0, 1);
			PT = self:CodeLabel(FunctionState, Reg, 1, 0);
			
			self:PatchToHere(FunctionState, (_K == "VJMP") and -1 or self:Jump(FunctionState));
		end;
		
		Final = self.GetLabel(FunctionState);
		
		self:PatchListAux(FunctionState, F, Final, Reg, PF);
		self:PatchListAux(FunctionState, T, Final, Reg, PT);
	end;
	
	Expression.F = -1;
	Expression.T = -1;
	
	Expression.Info = Reg;
	Expression.K    = "VNONRELOC";
end;

function K:Expression2NextReg(FunctionState, Expression)
	self:DischargeVars(FunctionState, Expression);
	self:FreeExpression(FunctionState, Expression);
	self:ReserveRegs(FunctionState, 1);
	self:Expression2Reg(FunctionState, Expression, FunctionState.FreeReg - 1);
end;

function K:Expression2AnyReg(FunctionState, Expression)
	self:DischargeVars(FunctionState, Expression);

	local Info = Expression.Info;
	local _K   = Expression.K;
	
	if _K == "VNONRELOC" then
		if not self:HasJumps(Expression) then  -- exp is already in a register
			return Info;
		end;
		
		if Info >= FunctionState.NactVar then
			self:Exp2Reg(FunctionState, Expression, Info);
			
			return Info;
		end;
	end;
	
	self:Exp2NextReg(FunctionState, Expression);
	
	return Info;
end;

function K:Expression2Val(FunctionState, Expression)
	if self:HasJumps(Expression) then
		return self:Expression2AnyReg(FunctionState, Expression);
	end;

	self:DischargeVars(FunctionState, Expression);
end;

function K:Expression2RK(FunctionState, Expression)
	self:Expression2Val(FunctionState, Expression);
	
	local _K   = Expression.K;
	local Info = Expression.Info;

	if K == "VK" then
		if Info <= MaxIndexRK then
			return P:RKAsk(Info);
		end;
	end;
	
	if K == "VKNUM" or K == "VTRUE" or K == "VFALSE" or K == "VNIL" then
		if FunctionState.NK <= MaxIndexRK then
			if K == "VNIL" then
				Expression.Info = self:NilK(FunctionState);
			else
				Expression.Info = (K == "VKNUM") and self:NumberK(FunctionState, Expression.NVal) or self:BoolK(FunctionState, K == "VTRUE");
			end;
			
			Expression.K = "VK";
			
			return P:RKAsk(Expression.Info);
		end;
	end;
	
	return self:Expression2AnyReg(FunctionState, Expression);
end;

function K:StoreVar(FunctionState, Var, Expression)
	local _K   = Var.K;
	local Info = Var.Info;

	if _K == "VLOCAL" then
		self:FreeExpression(FunctionState, Expression);
		self:Expression2Reg(FunctionState, Expression, Info);

		return;
	end;

	local E;

	if _K == "VUPVAL" then
		E = self:Expression2AnyReg(FunctionState, Expression);

		self:CodeABC(FunctionState, "OP_SETUPVAL", E, Info, 0);
	elseif _K == "VGLOBAL" then
		E = self:Expression2AnyReg(FunctionState, Expression);

		self:CodeABx(FunctionState, "OP_SETGLOBAL", E, Info);
	elseif _K == "VINDEXED" then
		E = self:Expression2RK(FunctionState, Expression);

		self:CodeABC(FunctionState, "OP_SETTABLE", Info, Var.Aux, E);
	else
		lua_Assert(0);
	end;

	self:FreeExpression(FunctionState, Expression);
end;

function K:_self(FunctionState, Expression, Key)
	self:Expression2AnyReg(FunctionState, Expression);
	self:FreeExpression(FunctionState, Expression);

	local Function = FunctionState.FreeReg;

	self:ReserveRegs(FunctionState, 2)
	self:CodeABC(FunctionState, "OP_SELF", Function, Expression.Info, self:Expression2RK(FunctionState, Key));
	self:FreeExpression(FunctionState, Key);

	Expression.Info = Function;
	Expression.K = "VNONRELOC";
end;

function K:InvertJump(FunctionState, Expression)
	local Pc = self.GetJumpControl(FunctionState, Expression.Info);

	local Opcode = P:GET_OPCODE(Pc);

	lua_Assert(P:TestTMode(Opcode) ~= 0 and
		Opcode ~= "OP_TESTSET" and
		Opcode ~= "OP_TEST");

	Pc.A = (Pc.A == 0) and 1 or 0;
end;

function K:JumpOnCondition(FunctionState, Expression, Condition)
	if Expression.K == "VRELOCABLE" then
		local Code = self.GetCode(FunctionState, Expression);

		if Code.OP == "OP_NOT" then
			FunctionState.pc = FunctionState.pc - 1; -- remove previous OP_NOT

			return self:ConditionalJump(FunctionState, "OP_TEST", Code.B, 0, Condition and 0 or 1);
		end;
	end;

	self:Discharge2AnyReg(FunctionState, Expression);
	self:FreeExpression(FunctionState, Expression);

	return self:ConditionalJump(FunctionState, "OP_TESTSET", NO_REG, Expression.Info, Condition and 1 or 0);
end;

function K:GoIfTrue(FunctionState, Expression)
	local Pc;  -- pc of last jump

	self:DischargeVars(FunctionState, Expression);

	local _K = Expression.K;

	if _K == "VK" or _K == "VKNUM" or _K == "VTRUE" then
		Pc = NO_JUMP;  -- always true; do nothing
	elseif _K == "VFALSE" then
		Pc = self:Jump(FunctionState); -- always jump
	elseif _K == "VJMP" then
		self:InverJump(FunctionState, Expression);

		Pc = Expression.info
	else
		Pc = self:JumpOnCondition(FunctionState, Expression, false);
	end;

	Expression.F = self:Concat(FunctionState, Expression.F, Pc); -- insert last jump in `f' list

	self:PatchToHere(FunctionState, Expression.T);

	Expression.T = NO_JUMP;
end;

function K:GoIfFalse(FunctionState, Expression)
	local Pc;  -- pc of last jump

	self:DischargeVars(FunctionState, Expression);

	local _K = Expression.K;

	if _K == "VNIL" or _K == "VFALSE"then
		Pc = NO_JUMP;  -- always false; do nothing
	elseif _K == "VTRUE" then
		Pc = self:Jump(FunctionState); -- always jump
	elseif _K == "VJMP" then
		Pc = Expression.Info;
	else
		Pc = self:JumpOnCondition(FunctionState, Expression, true);
	end;

	FunctionState.T = self:Concat(FunctionState, Expression.T, Pc); -- insert last jump in `t' list

	self:PatchToHere(FunctionState, Expression.F);

	FunctionState.F = NO_JUMP;
end;

function K:CodeNot(FunctionState, Expression)
	self:DischargeVars(FunctionState, Expression);

	local _K = Expression.K;

	if _K == "VNIL" or _K == "VFALSE" then
		Expression.K = "VTRUE";
	elseif _K == "VK" or _K == "VKNUM" or _K == "VTRUE" then
		Expression.K = "VFALSE";
	elseif _K == "VJMP" then
		self:InvertJump(FunctionState, Expression)
	elseif _K == "VRELOCABLE" or _K == "VNONRELOC" then
		self:Discharge2AnyReg(FunctionState, Expression);
		self:FreeExpression(FunctionState, Expression);

		Expression.Info = self:CodeABC(FunctionState, "OP_NOT", 0, Expression.info, 0);
		Expression.K    = "VRELOCABLE";
	else
		lua_Assert(0); -- cannot happen
	end;

	-- interchange true and false lists

	local OldF = Expression.F;
	local OldT = Expression.T;

	local NewF = OldT;
	local NewT = OldF;

	Expression.F = NewF;
	Expression.T = NewT;

	self:RemoveValues(FunctionState, NewF);
	self:RemoveValues(FunctionState, NewT);
end;

function K:Indexed(FunctionState, T, _K)
	T.Aux = self:Expression2RK(FunctionState, _K);
	T.K = "VINDEXED";
end;

function K:ConstFolding(Opcode, E1, E2)
	local NVal = 0;

	local IsNumeral = self.IsNumeral;

	if not IsNumeral(E1) or not IsNumeral(E2) then return; end;

	local V1 = E1.NVal;
	local V2 = E2.NVal;

	if Opcode == "OP_LEN" then
		return; -- no constant folding for 'len'
	end

	if Opcode == "OP_ADD" then
		if V1 == 0 then
			NVal = V2;
		elseif V2 == 0 then
			NVal = V1;
		else
			NVal = V1 + V2;
		end;
	elseif Opcode == "OP_SUB" then
		if V1 == 0 then
			NVal = -V2;
		elseif V2 == 0 then
			NVal = V1;
		else
			NVal = V1 - V2;
		end;
	elseif Opcode == "OP_MUL" then
		if V1 == 0 or V2 == 0 then
			NVal = 0;
		else
			NVal = V1 * V2;
		end;
	elseif Opcode == "OP_DIV" then
		if V2 == 0 then -- do not attempt to mod by 0
			return;
		end;

		if V1 == 0 then
			NVal = V1;
		else
			NVal = V1 / V2;
		end;
	elseif Opcode == "OP_MOD" then
		if V2 == 0 then -- do not attempt to mod by 0
			return;
		end;

		if V1 == 0 then
			NVal = V1;
		else
			NVal = V1 % V2;
		end;
	elseif Opcode == "OP_POW" then
		if V1 == 0 then
			NVal = V1;
		elseif V2 == 0 then
			NVal = 1;
		else
			NVal = V1 ^ V2;
		end;
	elseif Opcode == "OP_UNM" then
		NVal = -V1;
	end;

	if NVal ~= NVal then -- do not attempt to produce NaN
		return;
	end;

	E1.NVal = NVal;

	return true;
end;

function K:CodeArithmetic(FunctionState, Opcode, E1, E2)
	if self:ConstFolding(Opcode, E1, E2) then
		return;
	end;

	local O1 = self:Expression2RK(FunctionState, E1);
	local O2 = (Opcode ~= "OP_UNM" and Opcode ~= "OP_LEN") and self:Expression2RK(FunctionState, E2) or 0;

	local IsGreater = O1 > O2;

	self:FreeExpression(FunctionState, IsGreater and E1 or E2);
	self:FreeExpression(FunctionState, IsGreater and E2 or E1);

	E1.Info = self:CodeABC(FunctionState, Opcode, 0, O1, O2);
	E1.K    = "VRELOCABLE";
end;

function K:CodeComparitor(FunctionState, Opcode, Condition, E1, E2)
	local O1 = self:Expression2RK(FunctionState, E1);
	local O2 = self:Expression2RK(FunctionState, E2);

	self:FreeExpression(FunctionState, E2);
	self:FreeExpression(FunctionState, E1);

	if Condition == 0 and Opcode ~= "OP_EQ" then
		O1, O2 = O2, O1;
		Condition = 1;
	end;

	E1.Info = self:ConditionalJump(FunctionState, Opcode, Condition, O1, O2);
	E1.K    = "VJMP";
end

------------------------------------------------------------------------
--
-- * used only in (lparser) luaY:subexpr()
------------------------------------------------------------------------
function K:Prefix(FunctionState, Opcode, Expression)
	local E2 = {
		T = NO_JUMP,
		F = NO_JUMP,
		K = "VKNUM",

		NVal = 0,
	};

	if Opcode == "OPR_MINUS" then
		if not self.IsNumeral(Expression) then
			self:Expression2AnyReg(FunctionState, Expression);  -- cannot operate on non-numeric constants
		end;

		return self:CodeArithmetic(FunctionState, "OP_UNM", Expression, E2);
	elseif Opcode == "OPR_NOT" then
		return self:CodeNot(FunctionState, Expression);
	elseif Opcode == "OPR_LEN" then
		self:Expression2AnyReg(FunctionState, Expression);  -- cannot operate on constants
		return self:CodeArithmetic(FunctionState, "OP_LEN", Expression, E2);
	end;

	lua_Assert(0);
end;

------------------------------------------------------------------------
--
-- * used only in (lparser) luaY:subexpr()
------------------------------------------------------------------------
function K:InFix(FunctionState, Opcode, V)
	if Opcode == "OPR_AND" then -- If only switch statements existed...
		return self:GoIfTrue(FunctionState, V);
	elseif Opcode == "OPR_OR" then
		return self:GoIfFalse(FunctionState, V);
	elseif Opcode == "OPR_CONCAT" then
		return self:Expression2NextReg(FunctionState, V);  -- operand must be on the 'stack'
	elseif Opcode == "OPR_ADD" or Opcode == "OPR_SUB" or Opcode == "OPR_MUL" or Opcode == "OPR_DIV" or Opcode == "OPR_MOD" or Opcode == "OPR_POW" then
		if not self.IsNumeral(V) then
			return self:Expression2RK(FunctionState, V);
		end;

		return;
	end;

	self:Expression2RK(FunctionState, V);
end;

------------------------------------------------------------------------
--
-- * used only in (lparser) luaY:subexpr()
------------------------------------------------------------------------
-- table lookups to simplify testing
local ArithmeticOpcodes = {
	OPR_ADD = "OP_ADD", OPR_SUB = "OP_SUB", OPR_MUL = "OP_MUL",
	OPR_DIV = "OP_DIV", OPR_MOD = "OP_MOD", OPR_POW = "OP_POW",
};

local ComparitorOpcodes = {
	OPR_EQ = "OP_EQ", OPR_NE = "OP_EQ", OPR_LT = "OP_LT",
	OPR_LE = "OP_LE", OPR_GT = "OP_LT", OPR_GE = "OP_LE",
};

local ComparitorConditions = {
	OPR_EQ = 1, OPR_NE = 0, OPR_LT = 1,
	OPR_LE = 1, OPR_GT = 0, OPR_GE = 0,
};

local function K_CopyExpression(E1, E2)
	for Idx, Val in pairs(E2) do
		E1[Idx] = Val;
	end;
end;

function K:PositionFix(FunctionState, Opcode, E1, E2)
	if Opcode == "OPR_AND" then
		lua_Assert(E1.t == NO_JUMP); -- list must be closed

		self:DischargeVars(FunctionState, E2);

		E2.F = self:concat(FunctionState, E2.F, E1.F);

		return K_CopyExpression(E1, E2);
	end;
	
	if Opcode == "OPR_OR" then
		lua_Assert(E1.f == NO_JUMP); -- list must be closed

		self:DischargeVars(FunctionState, E2);

		E2.t = self:Concat(FunctionState, E2.T, E1.T);

		return K_CopyExpression(E1, E2);
	end;

	if Opcode == "OPR_CONCAT" then
		self:Expression2Val(FunctionState, E2);

		local Instr = self.GetCode(FunctionState, E2);

		if E2.K == "VRELOCABLE" then
			if P:GET_OPCODE(Instr) == "OP_CONCAT" then
				lua_Assert(E1.Info == Instr.B - 1);

				self:FreeExpression(FunctionState, E1);

				Instr.B = E1.Info;

				E1.K = "VRELOCABLE";
				E1.Info = E2.Info;

				return;
			end;
		end;
		
		self:Expression2NextReg(FunctionState, E2);  -- operand must be on the 'stack'
		return self:CodeArithmetic(FunctionState, "OP_CONCAT", E1, E2);
	end;
	
	local Arithmetic = ArithmeticOpcodes[Opcode];

	if Arithmetic then
		return self:CodeArithmetic(FunctionState, Arithmetic, E1, E2);	
	end;

	local Comparitor = ComparitorOpcodes[Opcode];

	if Comparitor then
		return self:CodeComparitor(FunctionState, Comparitor, ComparitorConditions[Opcode], E1, E2);
	end;

	lua_Assert(0);
end;

------------------------------------------------------------------------
-- adjusts debug information for last instruction written, in order to
-- change the line where item comes into existence
-- * used in (lparser) luaY:funcargs(), luaY:forbody(), luaY:funcstat()
------------------------------------------------------------------------
function K:FixLine(FunctionState, Line)
	FunctionState.F.LineInfo[FunctionState.Pc - 1] = Line;
end

------------------------------------------------------------------------
-- general function to write an instruction into the instruction buffer,
-- sets debug information too
-- * used in luaK:codeABC(), luaK:codeABx()
-- * called directly by (lparser) luaY:whilestat()
------------------------------------------------------------------------
function K:Code(FunctionState, I, Line)
	local F        = FunctionState.F;
	local LuaState = FunctionState.LuaState;
	local Pc       = FunctionState.Pc;

	local Code     = F.Code;
	local LineInfo = F.LineInfo;

	self:DischargeJPC(FunctionState); -- 'pc' will change

	-- put new instruction in code array

	Y:GrowVector(LuaState, Code, Pc, F.SizeCode, NIL, MaxInt, "code size overflow");

	Code[Pc] = I;

	-- save corresponding line information

	Y:GrowVector(LuaState, LineInfo, Pc, F.SizeLineInfo, NIL, MaxInt, "code size overflow");

	LineInfo[Pc] = Line;
	
	FunctionState.Pc = Pc + 1;

	return Pc;
end

local MaskN = OpArgMask.OpArgN;

function K:CodeABC(FunctionState, Opcode, A, B, C)
	lua_Assert(P:GetOpMode(Opcode) == OpMode.iABC);
	lua_Assert(P:GetBMode(OpCode) ~= MaskN or B == 0);
	lua_Assert(P:GetCMode(OpCode) ~= MaskN or C == 0);

	return self:Code(FunctionState, P:CREATE_ABC(Opcode, A, B, C), FunctionState.LexerState.LastLine);
end;

function K:CodeABx(FunctionState, Opcode, A, Bx)
	local Opmode = P:GetOpMode(Opcode);

	lua_Assert(Opmode == OpMode.iABx or Opmode == OpMode.iAsBx);
	lua_Assert(P:GetCMode(Opcode) == MaskN);

	return self:Code(FunctionState, P:CREATE_ABx(Opcode, A, Bx), FunctionState.LexerState.LastLine);
end;

function K:SetList(FunctionState, Base, NumberOfElements, ToStore)
	local C = (NumberOfElements - 1) / FieldsPerFlush;
	C = (C - (C % 1)) + 1; -- Faster int parsing equation than math.floor

	local B = (ToStore == MultipleReturn) and 0 or ToStore;
	lua_Assert(ToStore ~= 0);

	if C <= MAXARG_C then
		self:CodeABC(FunctionState, "OP_SETLIST", Base, B, C);
	else
		self:CodeABC(FunctionState, "OP_SETLIST", Base, B, 0);
		self:Code(FunctionState, P:CREATE_Inst(C), FunctionState.LexerState.LastLine);
	end;

	FunctionState.FreeReg = Base + 1; -- free registers with list values
end;

function Y:LUA_QL(x)
	return Format("'%s'", x);
end;

function Y:GrowVector(LuaState, V, NumberOfElements, Size, T, Limit, Message)
	return (NumberOfElements >= Limit) and error(Message or "overran limit!") or NumberOfElements;
end;

function Y:NewProto() -- It never needed the state as an argument?
	local FunctionState = {};

	FunctionState.Source = nil;

	FunctionState.LineDefined     = 0;
	FunctionState.LastLineDefined = 0;
	FunctionState.MaxStackSize    = 0;
	FunctionState.NUps            = 0;
	FunctionState.NumParams       = 0;

	FunctionState.IsVararg = 0;
	
	FunctionState.K        = {};
	FunctionState.P        = {};
	FunctionState.Code     = {};
	FunctionState.Upvalues = {};
	FunctionState.LineInfo = {};
	FunctionState.LocVars  = {};

	FunctionState.SizeK        = 0;
	FunctionState.SizeP        = 0;
	FunctionState.SizeCode     = 0;
	FunctionState.SizeUpvalues = 0;
	FunctionState.SizeLineInfo = 0;
	FunctionState.SizeLocVars  = 0;

	return FunctionState;
end;

function Y:Int2FloatingPoint(x)
	local Exponent = 0;

	while x >= 16 do
		x = (x + 1) / 2;
		x = x - (x % 1);

		Exponent = Exponent + 1;
	end;

	if x < 8 then return x; end;
	return ((Exponent + 1) * 8) + (x - 8);
end;

function Y:HasMultipleReturns(K)
	return K == "VCALL" or K == "VVARARG;"
end;

function Y:GetLocalVar(FunctionState, Idx)
	return FunctionState.F.LocVars[FunctionState.ActVars[Idx]];
end;

function Y:CheckLimit(FunctionState, Value, Limit, Message)
	return (Value > Limit and self:ErrorLimit(FunctionState, Limit, Message)) or Value;
end;

function Y:AnchorToken()
	--[[
	local Token = LexerState.T.Token;

	if Token == "TK_NAME" or Token == "TK_STRING" then
		-- not relevant to Lua implementation of parser
		-- luaX_newstring(ls, getstr(ts), ts->tsv.len); /* C */
	end;
	]]
end;

function Y:ErrorExpected(LexerState, Token)
	X:SyntaxError(LexerState, Format("'%s' expected", X.Token2Str(LexerState, Token)));
end;

local LimitErrMessage1 = "main function has more than %d '%s'";
local LimitErrMessage2 = "function at line %d has more than %d '%s'";

function Y:ErrorLimit(FunctionState, Limit, What)
	local LineDefined = FunctionState.F.LineDefined;

	X:LexError(FunctionState.LexerState, LineDefined == 0 and Format(LimitErrMessage1, Limit, What) or Format(LimitErrMessage2, LineDefined, Limit, What), 0);
end;
function Y:TestNext(LexerState, C)
	local Condition = LexerState.T.Token == C;

	if Condition then
		X:Next(LexerState);
	end;

	return Condition;
end;

function Y:Check(LexerState, C)
	if LexerState.T.Token ~= C then
		self:error_expected(LexerState, C);
	end;
end;

function Y:CheckNext(LexerState, C)
	if LexerState.T.Token ~= C then
		self:ErrorExpected(LexerState, C);
	end;

	X:Next(LexerState);
end;

function Y:CheckCondition(LexerState, Condition, Message)
	return Condition or X:SyntaxError(LexerState, Message);
end;

function Y:CheckMatch(LexerState, What, Who, Where)
	self:TestNext(LexerState, What);

	if Where == LexerState.LineNumber then
		self:ErrorExpected(LexerState, What);
	end;

	X:SyntaxError(LexerState, Format("%s expected (to close '%s' at line %d)", X:Token2Str(What), X:Token2Str(Who), Where));
end;

function Y:CheckStringName(LexerState)
	self:Check(LexerState, "TK_NAME");
	local SemInfo = LexerState.T.SemInfo;

	X:Next(LexerState);

	return SemInfo;
end;

function Y:InitExpression(Expression, _K, Info)
	Expression.F    = NO_JUMP;
	Expression.T    = NO_JUMP;
	Expression.K    = _K;
	Expression.Info = Info;
end;

function Y:CodeString(LexerState, Expression, String)
	self:InitExpression(Expression, "VK", K:StringK(LexerState.FunctionState, String));
end;

function Y:CheckName(LexerState, Expression)
	self:CodeString(LexerState, Expression, self:CheckStringName(LexerState));
end;

function Y:RegisterLocalVar(LexerState, VarName)
	local F             = LexerState.F;
	local FunctionState = LexerState.FunctionState;

	self:GrowVector(LexerState.L, F.LocVars, FunctionState.nlocvars, F.SizeLocVars, nil, self.SHRT_MAX, "too many local variables");
	-- loop to initialize empty f.locvar positions not required

	local NLocVars = FunctionState.NLocVars;

	F.LocVars[NLocVars] = { VarName = VarName }; -- LocVar

	NLocVars = NLocVars + 1;

	FunctionState.NLocVars = NLocVars;

	return NLocVars;
end;

function Y:NewLocalVarLiteral(...)
	self:NewLocalVar(...);
end;

function Y:NewLocalVar(LexerState, Name, N)
	local FunctionState = LexerState.FunctionState;

	local NewNactVar = FunctionState.NactVar + N;

	self:CheckLimit(FunctionState, NewNactVar + 1, self.LUAI_MAXVARS, "local variables");

	FunctionState.ActVar[NewNactVar] = self:RegisterLocalVar(LexerState, Name);
end;

function Y:AdjustLocalVars(LexerState, NVars)
	local FunctionState = LexerState.FunctionState;
	local NactVar       = FunctionState.NactVar;
	local Pc            = FunctionState.Pc;

	FunctionState.NactVar = NactVar + NVars;

	for Idx = NVars, 1, -1 do
		self:GetLocalVar(FunctionState, NactVar - Idx).StartPc = Pc;
	end;
end;

function Y:AdjustLocalVarsFromFS(FunctionState, NVars)
	local NactVar       = FunctionState.NactVar;
	local Pc            = FunctionState.Pc;

	FunctionState.NactVar = NactVar + NVars;

	for Idx = NVars, 1, -1 do
		self:GetLocalVar(FunctionState, NactVar - Idx).StartPc = Pc;
	end;
end;

function Y:RemoveVars(LexerState, ToLevel)
	local FunctionState = LexerState.FunctionState;
	local NactVar       = FunctionState.NactVar;
	local Pc            = FunctionState.Pc;

	while NactVar > ToLevel do
		NactVar = NactVar - 1;

		FunctionState.NactVar = NactVar;
		
		self:GetLocVar(FunctionState, NactVar).EndPc = Pc;
	end;
end;

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
function Y:OpenFunction(ls, fs)
	local L = ls.L;
	local F = self:NewProto(L);

	fs.F    = F;
	fs.Prev = ls.Fs;  -- linked list of funcstates
	fs.Ls   = ls;
	fs.L    = L;
	ls.Fs   = fs;
	fs.Pc   = 0;

	fs.LastTarget = NO_JUMP;
	fs.Jpc        = NO_JUMP;
	fs.FreeReg    = 0;

	fs.Nk = 0;
	fs.Np = 0;

	fs.NLocVars = 0;
	fs.NactVar  = 0;

	fs.Bl = nil;

	fs.H = {};  -- constant table; was luaH_new call

	F.MaxStackSsizeource        = ls.source;
	F.MaxStackSsize = 2; -- registers 0/1 are always valid
end

------------------------------------------------------------------------
-- closing of a function
------------------------------------------------------------------------
function Y:CloseFunction(ls)
	local L  = ls.L;
	local fs = ls.fs;
	local f  = fs.f;

	self:RemoveVars(ls, 0);
	K:Return(fs, 0, 0);

	local Pc = fs.Pc;

	f.Sizecode     = Pc;
	f.Sizelineinfo = Pc;

	f.SizeK = fs.Nk;
	f.SizeP = fs.Np;

	f.SizeLocVars  = fs.NLocVars;
	f.SizeUpvalues = f.NUps;

	assert(fs.bl == nil);

	ls.fs = fs.prev;

	if fs then
		self:AnchorToken(ls);
	end;
end

------------------------------------------------------------------------
-- parser initialization function
-- * note additional sub-tables needed for LexState, FuncState
------------------------------------------------------------------------
function Y:Parser(LuaState, Zio, Buff, Name)
	local LexerState    = {};
	local FunctionState = {};

	LexerState.T         = {};
	LexerState.LookAhead = {};

	FunctionState.Upvalues = {};
	FunctionState.ActVar   = {};

	LuaState.NumberCalls = 0;

	LexerState.Buff = Buff;
	X:SetInput(LuaState, LexerState, Zio, Name);

	self:OpenFunction(LexerState, FunctionState);

	local F = FunctionState.F;

	F.IsVararg = VarargIsVararg;  -- main func. is always vararg
	X:Next(LexerState);  -- read first token

	self:Chunk(LexerState);
	self:Check(LexerState, "TK_EOS");

	self:CloseFunction(LexerState);

	lua_Assert(F.NUps == 0);
	
	lua_Assert(FunctionState.Prev == nil);
	lua_Assert(FunctionState.FunctionState == nil);

	return F;
end

--[[--------------------------------------------------------------------
-- GRAMMAR RULES
----------------------------------------------------------------------]]

------------------------------------------------------------------------
-- parse a function name suffix, for function call specifications
-- * used in primaryexp(), funcname()
------------------------------------------------------------------------
function Y:field(ls, v)
	-- field -> ['.' | ':'] NAME
	local fs = ls.fs
	local key = {}  -- expdesc
	K:exp2anyreg(fs, v)
	X:next(ls)  -- skip the dot or colon
	self:checkname(ls, key)
	K:indexed(fs, v, key)
end

------------------------------------------------------------------------
-- parse a table indexing suffix, for constructors, expressions
-- * used in recfield(), primaryexp()
------------------------------------------------------------------------
function Y:yindex(ls, v)
	-- index -> '[' expr ']'
	X:Next(ls);  -- skip the '['
	self:expr(ls, v);
	K:Expression2Val(ls.fs, v);
	self:checknext(ls, "]");
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
function Y:recfield(ls, cc)
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
function Y:SimpleExpression(LexerState, V)
	-- simpleexp -> NUMBER | STRING | NIL | TRUE | FALSE | ... |
	--              constructor | FUNCTION body | primaryexp
	local T = LexerState.T;
	local C = T.Token;

	if C == "TK_NUMBER" then
		self:InitExpression(V, "VKNUM", 0);

		V.NVal = T.SemInfo;
	elseif c == "TK_STRING" then
		self:CodeString(LexerState, V, T.SemInfo);
	elseif c == "TK_NIL" then
		self:InitExpression(V, "VNIL", 0);
	elseif c == "TK_TRUE" then
		self:InitExpression(V, "VTRUE", 0);
	elseif c == "TK_FALSE" then
		self:InitExpression(V, "VFALSE", 0);
	elseif c == "TK_DOTS" then  -- vararg
		local FunctionState = LexerState.fs;
		local Function      = FunctionState.F;
		local IsVararg      = Function.IsVararg;

		self:CheckCondition(FunctionState, IsVararg ~= 0, "cannot use "..self:LUA_QL("...").." outside a vararg function");

		local VARARG_NEEDSARG = self.VARARG_NEEDSARG;

		if IsVararg >= VARARG_NEEDSARG then
			Function.IsVararg = IsVararg - VARARG_NEEDSARG;  -- don't need 'arg'
		end;

		self:InitExpression(V, "VVARARG", K:CodeABC(FunctionState, "OP_VARARG", 0, 1, 0));
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
function Y:GetUnaryOperator(Op)
	if Op == "TK_NOT" then
		return "OPR_NOT";
	end;

	if Op == "TK_NOT" then
		return "OPR_NOT";
	end;

	return (Op == "-" and "OPR_MINUS") or (Op == "#" and "OPR_LEN") or "OPR_NOUNOPR";
end;

------------------------------------------------------------------------
-- Translates binary operator tokens if found, otherwise returns
-- OPR_NOBINOPR. Code generation uses OPR_* style tokens.
-- * used in subexpr()
------------------------------------------------------------------------
Y.getbinopr_table = {
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
function Y:chunk(ls)
	-- chunk -> { stat [';'] }
	local islast = false
	self:enterlevel(ls)
	while not islast and not self:block_follow(ls.t.token) do
		islast = self:statement(ls)
		self:testnext(ls, ";")
		lua_Assert(ls.fs.f.maxstacksize >= ls.fs.freereg and
							 ls.fs.freereg >= ls.fs.nactvar)
		ls.fs.freereg = ls.fs.nactvar  -- free registers
	end
	self:leavelevel(ls)
end;

do
	--//----------------------------------------//--
	--* 
	--//----------------------------------------//--

	--//----------------------------------------//--
	--* Init some dependencies
	--//----------------------------------------//--

	for V in Gmatch(Reserved, "[^\n]+") do
		local _, _, Tok, Str = Find(V, "(%S+)%s+(%S+)");
	
		LexerTokens[Tok] = Str;
		LexerEnums[Str]  = Tok;
	end;

	for V in Gmatch(InstrString, "%S+") do
		local Name = "OP_" .. V;
		
		OpCode[Name]    = Amount;
		OpNames[Amount] = V;
		ROpCode[Amount] = Name;
				
		Amount = Amount + 1;
	end;

	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iABC"));	 -- OP_MOVE
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgN", "iABx"));	 -- OP_LOADK
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgU", "iABC"));   -- OP_LOADBOOL
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iABC"));   -- OP_LOADNIL
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgN", "iABC"));   -- OP_GETUPVAL
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgN", "iABx"));   -- OP_GETGLOBAL
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgK", "iABC"));   -- OP_GETTABLE
	Insert(OpModes, Opmode(0, 0, "OpArgK", "OpArgN", "iABx"));   -- OP_SETGLOBAL
	Insert(OpModes, Opmode(0, 0, "OpArgU", "OpArgN", "iABC"));   -- OP_SETUPVAL
	Insert(OpModes, Opmode(0, 0, "OpArgK", "OpArgK", "iABC"));   -- OP_SETTABLE
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgU", "iABC"));   -- OP_NEWTABLE
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgK", "iABC"));   -- OP_SELF
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_ADD
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_SUB
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_MUL
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_DIV
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_MOD
	Insert(OpModes, Opmode(0, 1, "OpArgK", "OpArgK", "iABC"));   -- OP_POW
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iABC"));   -- OP_UNM
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iABC"));   -- OP_NOT
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iABC"));   -- OP_LEN
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgR", "iABC"));   -- OP_CONCAT
	Insert(OpModes, Opmode(0, 0, "OpArgR", "OpArgN", "iAsBx"));  -- OP_JMP
	Insert(OpModes, Opmode(1, 0, "OpArgK", "OpArgK", "iABC"));   -- OP_EQ
	Insert(OpModes, Opmode(1, 0, "OpArgK", "OpArgK", "iABC"));   -- OP_LT
	Insert(OpModes, Opmode(1, 0, "OpArgK", "OpArgK", "iABC"));   -- OP_LE
	Insert(OpModes, Opmode(1, 1, "OpArgR", "OpArgU", "iABC"));   -- OP_TEST
	Insert(OpModes, Opmode(1, 1, "OpArgR", "OpArgU", "iABC"));   -- OP_TESTSET
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgU", "iABC"));   -- OP_CALL
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgU", "iABC"));   -- OP_TAILCALL
	Insert(OpModes, Opmode(0, 0, "OpArgU", "OpArgN", "iABC"));   -- OP_RETURN
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"));  -- OP_FORLOOP
	Insert(OpModes, Opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"));  -- OP_FORPREP
	Insert(OpModes, Opmode(1, 0, "OpArgN", "OpArgU", "iABC"));   -- OP_TFORLOOP
	Insert(OpModes, Opmode(0, 0, "OpArgU", "OpArgU", "iABC"));   -- OP_SETLIST
	Insert(OpModes, Opmode(0, 0, "OpArgN", "OpArgN", "iABC"));   -- OP_CLOSE
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgN", "iABx"));   -- OP_CLOSURE
	Insert(OpModes, Opmode(0, 1, "OpArgU", "OpArgN", "iABC"));   -- OP_VARARG

	--//----------------------------------------//--
	--* Module functions
	--//----------------------------------------//--

	local LuaState = {};

	function Lua.Parse(Source, Name)
		return Y:Parser(Z_Init(Z_MakeStringReader(Source), NIL), NIL, "@" .. (Name or 'compiled-lua'));
	end;
	
	function Lua.DumpParserFunction(Function)
		local Writer, Buff = U_MakeStringSet();
		
		U:Dump(LuaState, Function, Writer, Buff);
	
		return Buff.Data;
	end;
	
	function Lua:Compile(...) -- Args: arg1: Source code, arg2: Source name (optional)
		return self.DumpParserFunction(self.Parse(...));
	end;
end;

return Lua;
