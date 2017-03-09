signature semanticsLib =
sig

    val decs_to_types_conv : Abbrev.conv
    val prog_to_top_types_conv : Abbrev.conv
    val prog_to_mods_conv : Abbrev.conv
    val no_dup_top_types_conv : Abbrev.conv
    val no_dup_mods_conv : Abbrev.conv

end
