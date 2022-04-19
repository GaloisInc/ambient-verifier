int bar2() {
  return 2;
}

int baz3() {
  return 3;
}

#define BAR_1_2 "BAR_1.2"
#define BAZ_1_1 "BAZ_1.1"

#define SYMVER( s ) \
    __asm__(".symver " s )

SYMVER( "bar2,bar@" BAR_1_2 );
SYMVER( "baz3,baz@@" BAZ_1_1 );
