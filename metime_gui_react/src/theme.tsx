import { createTheme, responsiveFontSizes } from "@mui/material";

const theme = responsiveFontSizes(createTheme({
  typography: {
    fontSize: 13,
  },
}));

export default theme;
