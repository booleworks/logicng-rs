#ifndef SHARPSAT_STATIC_STATE_H
#define SHARPSAT_STATIC_STATE_H

typedef unsigned char CA_SearchState;

class StaticState {
public:
    unsigned _bits_per_clause{0};
    unsigned _bits_per_variable{0}; // bitsperentry
    unsigned _bits_of_data_size{0}; // number of bits needed to store the data size
    unsigned _data_size_mask{0};
    unsigned _variable_mask{0};
    unsigned _clause_mask{0};
    const unsigned _bits_per_block= (sizeof(unsigned) << 3);
};

class ComponentArchetypeState {
public:
    CA_SearchState *seen_ = nullptr;
    unsigned seen_byte_size_ = 0;
};

#endif //SHARPSAT_STATIC_STATE_H
