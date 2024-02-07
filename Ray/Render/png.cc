// Minimal, Lean-friendly interface to libpng

#include <lean/lean.h>
#include <png.h>

extern "C" lean_obj_res
write_png(lean_object* path, uint32_t width, uint32_t height, lean_object* data) {
  // Declare variables at the front, since gotos will abound
  const char* error = "";
  FILE* file = 0;
  png_structp png = 0;
  png_infop info = 0;
  const int bit_depth = 8;
  const int color_type = PNG_COLOR_TYPE_RGB_ALPHA;

// If a check fails, we set an error message and jump to the end to close out
#define ASSERT(condition, message) if (!(condition)) { error = message; goto done; }

  // Ensure our dimensions are safe
  const uint32_t limit = 1 << 31;
  ASSERT(width < limit, "width must be < 2^31");
  ASSERT(height < limit, "height must be < 2^31");
  ASSERT(lean_sarray_size(data) == height * width * 4, "data.size != heigth * width * 4");

  // Set up libpng
  file = fopen(lean_string_cstr(path), "wb");
  ASSERT(file, "could not open file for writing");
  png = png_create_write_struct(PNG_LIBPNG_VER_STRING, 0, 0, 0);
  ASSERT(png, "could not create write struct");
  info = png_create_info_struct(png);
  ASSERT(info, "could not create info struct");
  ASSERT(!setjmp(png_jmpbuf(png)), "error writing .png");
  png_init_io(png, file);

  // Populate header information, and write
  png_set_IHDR(png, info, width, height, bit_depth, color_type, PNG_INTERLACE_NONE,
    PNG_COMPRESSION_TYPE_DEFAULT, PNG_FILTER_TYPE_DEFAULT);
  png_set_sRGB(png, info, PNG_sRGB_INTENT_PERCEPTUAL);
  png_write_info(png, info);

  // Write each row directly from the ByteArray.  The data must be in y-major, top to bottom order.
  for (uint32_t y = 0; y < height; y++)
    png_write_row(png, lean_sarray_cptr(data) + y * width * 4);
  png_write_end(png, info);

done:
  // All done!
  if (png || info)
    png_destroy_write_struct(&png, &info);
  if (file)
    fclose(file);
  return lean_mk_string(error);
}
