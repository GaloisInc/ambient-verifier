int bar1() {
  return 1;
}

#define BAR_1_1 "BAR_1.1"

#define SYMVER( s ) \
    __asm__(".symver " s )

SYMVER( "bar1,bar@@" BAR_1_1 );
