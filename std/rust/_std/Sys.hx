@:native("std.io.stdio")
extern class StdIo {
	static function print(s: String): Void;
	static function println(s: String): Void;
}

class Sys {
	public static function println(s: String) {
		StdIo.println(s);
	}
}